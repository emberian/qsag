//! OT scratch of the distributed guard setup is erased before its memory is released,
//! observed at the allocator: on a failed exchange, on a panicking transport, on a
//! refused answer and on completion.
use qsag_asm::wipe::SecretVec;
use qsag_policy::{
    BDOZ_PREPROC_SLOTS, PolicyAuthenticatedOt, PolicyGuardDkgRound1, PolicyGuardDkgRound2,
    PolicyGuardSeedOpenMsg, PolicyViolation, finalize_distributed_policy_guard,
};

/// Allocator hook: reports whether a watched heap block was all zero at the moment
/// it was handed back to the allocator.
mod freed_secret_watch {
    use std::alloc::{GlobalAlloc, Layout, System};
    use std::sync::atomic::{AtomicUsize, Ordering::SeqCst};

    const SLOTS: usize = 32;
    const FREE: usize = 0;
    const CLAIMED: usize = 1;
    const WATCHING: usize = 2;
    const FREED_ZERO: usize = 3;
    const FREED_DIRTY: usize = 4;
    static STATE: [AtomicUsize; SLOTS] = [const { AtomicUsize::new(FREE) }; SLOTS];
    static ADDR: [AtomicUsize; SLOTS] = [const { AtomicUsize::new(0) }; SLOTS];
    static LEN: [AtomicUsize; SLOTS] = [const { AtomicUsize::new(0) }; SLOTS];

    struct Watching;
    // SAFETY: every request is forwarded unchanged to the system allocator.
    unsafe impl GlobalAlloc for Watching {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            // SAFETY: the caller's contract is passed through.
            unsafe { System.alloc(layout) }
        }
        unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
            for slot in 0..SLOTS {
                if STATE[slot].load(SeqCst) == WATCHING && ADDR[slot].load(SeqCst) == ptr as usize {
                    let len = LEN[slot].load(SeqCst).min(layout.size());
                    // SAFETY: the block is still allocated here, and the watched prefix was
                    // initialized when it was registered.
                    let bytes = unsafe { core::slice::from_raw_parts(ptr, len) };
                    let verdict = if bytes.iter().all(|b| *b == 0) {
                        FREED_ZERO
                    } else {
                        FREED_DIRTY
                    };
                    STATE[slot].store(verdict, SeqCst);
                }
            }
            // SAFETY: the caller's contract is passed through.
            unsafe { System.dealloc(ptr, layout) }
        }
    }
    #[global_allocator]
    static ALLOCATOR: Watching = Watching;

    /// Watch the heap block that starts at `live`'s first element.
    pub fn watch<T>(live: &[T]) -> usize {
        assert!(!live.is_empty());
        for slot in 0..SLOTS {
            if STATE[slot]
                .compare_exchange(FREE, CLAIMED, SeqCst, SeqCst)
                .is_ok()
            {
                ADDR[slot].store(live.as_ptr() as usize, SeqCst);
                LEN[slot].store(core::mem::size_of_val(live), SeqCst);
                STATE[slot].store(WATCHING, SeqCst);
                return slot;
            }
        }
        panic!("no free watch slot");
    }

    /// `Some(true)` if the block was freed all zero, `Some(false)` if freed with content,
    /// `None` if it has not been freed. Releases the slot.
    pub fn outcome(slot: usize) -> Option<bool> {
        let verdict = match STATE[slot].load(SeqCst) {
            FREED_ZERO => Some(true),
            FREED_DIRTY => Some(false),
            _ => None,
        };
        STATE[slot].store(FREE, SeqCst);
        verdict
    }
}

use freed_secret_watch::{outcome, watch};

/// Records where the scratch handed to the OT lives, then fails, panics or answers.
enum Behave {
    Fail,
    Panic,
    Answer(usize),
}
struct WatchingOt {
    behave: Behave,
    watched: Vec<usize>,
}
impl PolicyAuthenticatedOt for WatchingOt {
    fn exchange(
        &mut self,
        _: u16,
        _: u16,
        _: [u8; 32],
        alternatives: &[[u128; 2]],
        choices: &[bool],
    ) -> Result<Vec<u128>, PolicyViolation> {
        assert_eq!(alternatives.len(), BDOZ_PREPROC_SLOTS * 256);
        assert!(alternatives.iter().all(|pair| *pair != [0; 2]));
        assert!(choices.iter().any(|bit| *bit));
        self.watched.push(watch(alternatives));
        self.watched.push(watch(choices));
        match self.behave {
            Behave::Fail => Err(PolicyViolation::BarrierBdozMacFailed),
            Behave::Panic => panic!("injected transport failure"),
            Behave::Answer(len) => {
                let answer = vec![u128::MAX; len];
                self.watched.push(watch(&answer));
                Ok(answer)
            }
        }
    }
}
fn dkg_ready() -> (PolicyGuardDkgRound2, Vec<PolicyGuardSeedOpenMsg>) {
    let (a, ac) = PolicyGuardDkgRound1::new(1, &[1, 2], [3; 32], [4; 32]).unwrap();
    let (b, bc) = PolicyGuardDkgRound1::new(2, &[1, 2], [3; 32], [5; 32]).unwrap();
    let (a, _) = a.round2_open_seeds(&bc).unwrap();
    let (_, bo) = b.round2_open_seeds(&ac).unwrap();
    (a, bo)
}
fn all_erased(ot: &WatchingOt, expected: usize) {
    assert_eq!(ot.watched.len(), expected);
    for &slot in &ot.watched {
        assert_eq!(outcome(slot), Some(true), "freed with secret bytes in it");
    }
}

#[test]
fn the_watch_reports_a_buffer_freed_with_its_contents() {
    let plain = vec![0xa5u8; 4096];
    let slot = watch(&plain);
    drop(plain);
    assert_eq!(outcome(slot), Some(false));
    let guarded = SecretVec::new(vec![0xa5u8; 4096]);
    let slot = watch(&guarded);
    drop(guarded);
    assert_eq!(outcome(slot), Some(true));
}

#[test]
fn ot_scratch_is_erased_before_release_on_error_unwind_and_completion() {
    let (state, opens) = dkg_ready();
    let mut ot = WatchingOt {
        behave: Behave::Fail,
        watched: Vec::new(),
    };
    assert!(finalize_distributed_policy_guard(state, &opens, &mut ot).is_err());
    all_erased(&ot, 2);

    let (state, opens) = dkg_ready();
    let mut ot = WatchingOt {
        behave: Behave::Panic,
        watched: Vec::new(),
    };
    let unwound = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = finalize_distributed_policy_guard(state, &opens, &mut ot);
    }));
    assert!(unwound.is_err());
    all_erased(&ot, 2);

    // A short answer is refused; the received values are erased all the same.
    let (state, opens) = dkg_ready();
    let mut ot = WatchingOt {
        behave: Behave::Answer(BDOZ_PREPROC_SLOTS * 256 - 1),
        watched: Vec::new(),
    };
    assert_eq!(
        finalize_distributed_policy_guard(state, &opens, &mut ot).err(),
        Some(PolicyViolation::BarrierBdozMacFailed)
    );
    all_erased(&ot, 3);

    let (state, opens) = dkg_ready();
    let mut ot = WatchingOt {
        behave: Behave::Answer(BDOZ_PREPROC_SLOTS * 256),
        watched: Vec::new(),
    };
    let guard = finalize_distributed_policy_guard(state, &opens, &mut ot).unwrap();
    all_erased(&ot, 3);
    drop(guard);
}
