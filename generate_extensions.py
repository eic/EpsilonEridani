import os
import glob

missing_files = [
    "EpsilonEridani/Mathematics/Distribution/Basic.lean",
    "EpsilonEridani/Mathematics/KroneckerDelta/Basic.lean",
    "EpsilonEridani/Particles/StandardModel/Fermions/DownSinglet.lean",
    "EpsilonEridani/Particles/StandardModel/Fermions/LeptonDoublet.lean",
    "EpsilonEridani/Particles/StandardModel/HiggsBoson/Basic.lean",
    "EpsilonEridani/QFT/PerturbationTheory/FeynmanDiagrams/Basic.lean",
    "EpsilonEridani/QFT/PerturbationTheory/WickAlgebra/NormalOrder/Basic.lean",
    "EpsilonEridani/Relativity/CliffordAlgebra.lean",
    "EpsilonEridani/Relativity/Fermions/Weyl/Contraction.lean",
    "EpsilonEridani/Relativity/Fermions/Weyl/DualLeftHanded.lean",
    "EpsilonEridani/Relativity/Fermions/Weyl/DualRightHanded.lean",
    "EpsilonEridani/Relativity/Fermions/Weyl/Duals.lean",
    "EpsilonEridani/Relativity/Fermions/Weyl/LeftHanded.lean",
    "EpsilonEridani/Relativity/Fermions/Weyl/Metric.lean",
    "EpsilonEridani/Relativity/Fermions/Weyl/RightHanded.lean",
    "EpsilonEridani/Relativity/Fermions/Weyl/Two.lean",
    "EpsilonEridani/Relativity/Fermions/Weyl/Unit.lean",
    "EpsilonEridani/Relativity/LorentzGroup/Restricted/FromBoostRotation.lean",
    "EpsilonEridani/Relativity/PauliMatrices/AsTensor.lean",
    "EpsilonEridani/Relativity/PauliMatrices/Relations.lean",
    "EpsilonEridani/Relativity/SL2C/Basic.lean",
    "EpsilonEridani/Relativity/Tensors/LeviCivita/Contractions.lean",
    "EpsilonEridani/Relativity/Tensors/RealTensor/Metrics/Basic.lean"
]

patch_dir = "/home/wdconinc/git/epsiloneridani-forks/patches"
patches = sorted(glob.glob(os.path.join(patch_dir, "*.patch")))

for mf in missing_files:
    # E.g. mf = EpsilonEridani/Mathematics/Distribution/Basic.lean
    # extensions file = EpsilonEridani/Mathematics/Distribution/Extensions.lean
    # wait, if mf is a file in the root of a module like CliffordAlgebra.lean,
    # extensions file = EpsilonEridani/Relativity/CliffordAlgebraExtensions.lean
    dirname = os.path.dirname(mf)
    basename = os.path.basename(mf).replace(".lean", "")
    ext_file = os.path.join(dirname, f"{basename}Extensions.lean")
    
    os.makedirs(dirname, exist_ok=True)
    
    # Original physlib import path
    physlib_import = mf.replace("EpsilonEridani/", "Physlib/").replace("/", ".").replace(".lean", "")
    
    hunks = []
    
    for patch in patches:
        with open(patch, "r", encoding="utf-8") as f:
            lines = f.readlines()
        
        in_file = False
        current_hunk = []
        for line in lines:
            if line.startswith("+++ b/" + mf):
                in_file = True
                current_hunk.append(f"-- Patch: {os.path.basename(patch)}\n")
            elif line.startswith("+++ b/"):
                in_file = False
            elif in_file:
                current_hunk.append(line)
        if current_hunk:
            hunks.append("".join(current_hunk))
    
    if hunks:
        with open(ext_file, "w", encoding="utf-8") as f:
            f.write(f"import {physlib_import}\n\n")
            f.write("/-\n")
            f.write("TODO: The following diffs represent upstream modifications to Physlib.\n")
            f.write("Port these additions as standalone lemmas/extensions in this file.\n")
            f.write("-/\n\n")
            for hunk in hunks:
                f.write("/-\n")
                f.write(hunk)
                f.write("-/\n\n")
                
