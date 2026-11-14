module Alex.InProject.ElementsCleanCases

open Fidelity.PSG

let acceptBoundary (imp: BoundaryImport) = imp
let acceptIntrinsic (w: IntrinsicWriteImport) = w
let acceptSpatial (s: SpatialModuleWitness) = s
let acceptScalar (b: BoundaryScalar) = b
