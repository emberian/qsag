import Obend.Apps.ZkNtt
#check Nat.add_mod
#check Nat.mul_mod
#check Obend.Apps.ZkNtt.glAdd_sound
#check Obend.Apps.ZkNtt.glSub_sound
#check Obend.Apps.ZkNtt.glCanon_sound
#check Obend.Hardware.HDL.WireM
example (a b c d : Nat) : (a+b+c+d)+(a+2*b)=2*a+3*b+c+d := by omega
