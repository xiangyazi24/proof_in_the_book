import ProofsInTheBook.ZinanFFCT105
import ProofsInTheBook.ZinanFFCT106

/-!
# Ch13 strict-arm monotonicity, reduced to the discrete Fenchel core

Composing the geometric reduction (FFCT106, `openedArmTurningLtTwoPi_of_core`) with the spherical
wiring (FFCT105, `spherical_arm_mono_ch13_of_turningBound`), Chapter 13's strict spherical
arm-monotonicity follows from the single pure-real-analysis residue `DiscreteFenchelCore`:
strictly-increasing lifted angles with gaps `< π`, positive edge lengths, and forward+backward
sine supports force the total turning `< 2π`.  This is exactly the discrete Fenchel theorem; it is
TRUE and non-vacuous (the geometric premises that instantiate it are inhabited — FFCT104
`premises_satisfiable`; numerically the turning maxes at `≈ 6.221 < 2π`).
-/

open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT104
open ProofsInTheBook.ZinanFFCT105
open ProofsInTheBook.ZinanFFCT106

namespace ProofsInTheBook.ZinanFFCT107

/-- **Chapter 13 strict-arm monotonicity from the discrete Fenchel core.**  The single remaining
residue of the whole chapter is `DiscreteFenchelCore`, a finite real-analysis statement carrying no
spherical / `det3` / complex machinery. -/
theorem spherical_arm_mono_ch13_of_discreteFenchel
    (hcore : DiscreteFenchelCore) :
    SphericalArmMonotone :=
  spherical_arm_mono_ch13_of_turningBound (openedArmTurningLtTwoPi_of_core hcore)

end ProofsInTheBook.ZinanFFCT107

#print axioms ProofsInTheBook.ZinanFFCT107.spherical_arm_mono_ch13_of_discreteFenchel
