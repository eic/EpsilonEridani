import os
import subprocess
import glob
import shutil

patch_dir = "/home/wdconinc/git/epsiloneridani-forks/patches"
repo_dir = "/home/wdconinc/git/epsiloneridani-forks/EpsilonEridani"
pending_dir = os.path.join(repo_dir, "PendingExtensions")

os.makedirs(pending_dir, exist_ok=True)
os.chdir(repo_dir)
subprocess.run(["git", "am", "--abort"], capture_output=True)

patches = sorted(glob.glob(os.path.join(patch_dir, "*.patch")))

for i, patch in enumerate(patches):
    patch_name = os.path.basename(patch)
    print(f"Applying [{i+1}/{len(patches)}] {patch_name}...")
    res = subprocess.run(["git", "am", "--reject", patch], capture_output=True, text=True)
    if res.returncode != 0:
        # Find all .rej files excluding PendingExtensions
        for root, dirs, files in os.walk(repo_dir):
            if "PendingExtensions" in root or ".git" in root:
                continue
            for f in files:
                if f.endswith(".rej"):
                    rej_path = os.path.join(root, f)
                    base = f
                    dest = os.path.join(pending_dir, f"{patch_name}_{base}")
                    shutil.move(rej_path, dest)
        
        subprocess.run(["git", "add", "-A"])
        cont_res = subprocess.run(["git", "am", "--continue"], capture_output=True, text=True)
        if "You have nothing to commit" in cont_res.stdout or cont_res.returncode != 0:
            subprocess.run(["git", "am", "--skip"], capture_output=True, text=True)

print("Patching complete.")
