import os
import subprocess
import glob
import shutil

patch_dir = "/home/wdconinc/git/epsiloneridani-forks/patches"
repo_dir = "/home/wdconinc/git/epsiloneridani-forks/EpsilonEridani"
pending_dir = os.path.join(repo_dir, "PendingExtensions")

os.makedirs(pending_dir, exist_ok=True)

# We are already inside the repo but let's be safe
os.chdir(repo_dir)

# Ensure no am in progress
subprocess.run(["git", "am", "--abort"], capture_output=True)

patches = sorted(glob.glob(os.path.join(patch_dir, "*.patch")))

# To apply all at once and handle failures:
for patch in patches:
    print(f"Applying {os.path.basename(patch)}...")
    res = subprocess.run(["git", "am", "--reject", patch], capture_output=True, text=True)
    if res.returncode != 0:
        print(f"  Conflict detected in {os.path.basename(patch)}")
        
        # Find all .rej files
        rejs = glob.glob("**/*.rej", recursive=True)
        for rej in rejs:
            # Move it to PendingExtensions
            base = os.path.basename(rej)
            dest = os.path.join(pending_dir, f"{os.path.basename(patch)}_{base}")
            shutil.move(rej, dest)
            print(f"  Saved rejected hunk to {dest}")
        
        # Now we need to remove the failed file modifications if they are just not existing
        # git am --reject might leave unstaged changes or untracked .rej. We moved .rej.
        # But if the file didn't exist, git just doesn't add it.
        # We want to commit whatever succeeded and move on.
        subprocess.run(["git", "add", "-A"])
        # If there's nothing to commit, git am --continue might complain or skip.
        # Usually git am --continue works if index is modified.
        # But if the patch ONLY contained rejected hunks (so index is empty),
        # git am --continue will fail with "You have nothing to commit".
        # In that case, git am --skip is needed.
        cont_res = subprocess.run(["git", "am", "--continue"], capture_output=True, text=True)
        if "You have nothing to commit" in cont_res.stdout or cont_res.returncode != 0:
            subprocess.run(["git", "am", "--skip"], capture_output=True, text=True)

print("Patching complete.")
