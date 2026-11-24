//! Operating-system entropy without a file descriptor.

use std::io::Error as OsRngError;
use std::io::ErrorKind;

/// Fill the entire destination or return the OS error. On error discard the
/// destination, which may have been partially filled.
pub fn fill_os_random(dest: &mut [u8]) -> Result<(), OsRngError> {
    // getentropy accepts up to 256 bytes. Linux getrandom also guarantees
    // whole small reads once initialized, but handle partial delivery anyway.
    if !cfg!(any(
        target_os = "linux",
        target_os = "android",
        target_vendor = "apple",
        target_os = "freebsd",
        target_os = "openbsd",
        target_os = "netbsd",
        target_os = "dragonfly"
    )) {
        return if dest.is_empty() {
            Ok(())
        } else {
            Err(ErrorKind::Unsupported.into())
        };
    }
    for mut chunk in dest.chunks_mut(256) {
        while !chunk.is_empty() {
            match read_entropy(chunk) {
                Ok(0) => return Err(ErrorKind::UnexpectedEof.into()),
                Ok(n) => chunk = &mut chunk[n..],
                // EINTR has value 4 on all of the Unix targets below.
                Err(4) => continue,
                Err(code) => return Err(OsRngError::from_raw_os_error(code)),
            }
        }
    }
    Ok(())
}

#[cfg(any(target_os = "linux", target_os = "android"))]
#[inline(never)]
fn read_entropy(dest: &mut [u8]) -> Result<usize, i32> {
    unsafe extern "C" {
        #[cfg_attr(target_os = "linux", link_name = "__errno_location")]
        #[cfg_attr(target_os = "android", link_name = "__errno")]
        fn errno_address() -> *const core::ffi::c_int;
        fn getrandom(buf: *mut core::ffi::c_void, len: usize, flags: core::ffi::c_uint) -> isize;
    }
    // SAFETY: the slice is exclusively writable for exactly len bytes.
    let n = unsafe { getrandom(dest.as_mut_ptr().cast(), dest.len(), 0) };
    // SAFETY: on failure libc has initialized errno for this thread.
    usize::try_from(n).map_err(|_| unsafe { *errno_address() })
}

#[cfg(any(
    target_vendor = "apple",
    target_os = "freebsd",
    target_os = "openbsd",
    target_os = "netbsd",
    target_os = "dragonfly"
))]
#[inline(never)]
fn read_entropy(dest: &mut [u8]) -> Result<usize, i32> {
    unsafe extern "C" {
        fn getentropy(buf: *mut core::ffi::c_void, len: usize) -> core::ffi::c_int;
    }
    // SAFETY: getentropy fills the writable slice on success, or sets errno.
    if unsafe { getentropy(dest.as_mut_ptr().cast(), dest.len()) } == 0 {
        Ok(dest.len())
    } else {
        Err(OsRngError::last_os_error()
            .raw_os_error()
            .expect("getentropy sets errno"))
    }
}

#[cfg(not(any(
    target_os = "linux",
    target_os = "android",
    target_vendor = "apple",
    target_os = "freebsd",
    target_os = "openbsd",
    target_os = "netbsd",
    target_os = "dragonfly"
)))]
fn read_entropy(_: &mut [u8]) -> Result<usize, i32> {
    unreachable!("unsupported targets return before the read")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn os_random_fills_multiple_chunks_and_accepts_empty_slices() {
        fill_os_random(&mut []).unwrap();
        let mut buf = [0; 769];
        fill_os_random(&mut buf).unwrap();
        assert!(
            buf[..768]
                .chunks(256)
                .all(|chunk| chunk.iter().any(|&b| b != 0))
        );
    }
}
