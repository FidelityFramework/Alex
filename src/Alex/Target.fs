/// The target vocabulary a host selects before witnessing. These are inputs to Alex;
/// a witness reads them and never derives one from the program.
module Alex.Target

/// Target platform: which family of target forms the witnesses spell.
type TargetPlatform =
    | CPU
    | FPGA
    | GPU
    | MCU
    | NPU
    | Library
