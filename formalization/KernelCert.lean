/-
  KernelCert: the soundness argument behind Certifaiger's safety checks for hardware
  model-checking witness circuits, and a reference checker compiled from it.

  * Circuit.lean, Witness.lean: circuits with constraints and reset functions that read
    inputs and latches; constrained runs and `Safe`; witnesses with shared latches and
    inputs; the five obligations.
  * Metatheorem.lean: `witness_sound`, safety from the five obligations.
  * Stratification.lean: the FMCAD'22 reset side condition; reset existence and relative
    determinacy.
  * Level2.lean: the combinational form of the checks; `UnmappedStratification`, the side
    condition of Certifaiger 10.3.0; `witness_sound_K`.
  * Diag.lean: Certifaiger's own form of the Transition check; it implies the mechanized
    one (`transCheckCF_implies_transCheckK`), hence `witness_sound_CF`.
  * Enum.lean, Decide.lean: deciding the checks by enumeration; `check_sound`.
  * Aig.lean: and-inverter graphs as circuits; the witness interface from index pairs.
  * Examples.lean, Counterexamples.lean: worked instances; the universal forms refuted.
  Axiom audit: AxiomsReport.lean.
-/
import KernelCert.Circuit
import KernelCert.Witness
import KernelCert.Stratification
import KernelCert.Metatheorem
import KernelCert.Level2
import KernelCert.Examples
import KernelCert.Counterexamples
import KernelCert.Enum
import KernelCert.Decide
import KernelCert.Aig
import KernelCert.Diag
