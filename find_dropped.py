import glob

# All files that exist in EpsilonEridani currently
import os
existing_files = set()
for root, dirs, files in os.walk('.'):
    for f in files:
        if f.endswith('.lean'):
            existing_files.add(os.path.relpath(os.path.join(root, f)))

patch_dir = "/home/wdconinc/git/epsiloneridani-forks/patches"
patches = sorted(glob.glob(os.path.join(patch_dir, "*.patch")))

dropped_modifications = set()
for patch in patches:
    with open(patch, 'r', encoding='utf-8') as f:
        lines = f.readlines()
        for line in lines:
            if line.startswith('+++ b/EpsilonEridani/'):
                filepath = line[6:].strip()
                if filepath not in existing_files:
                    dropped_modifications.add(filepath)

for filepath in sorted(dropped_modifications):
    print(filepath)
