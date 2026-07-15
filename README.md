# Lean Course Summer 2026

This repository contains Lean files for the summer 2026 course.

## Installing Lean

The recommended way to install Lean is to follow the official instructions at
<https://lean-lang.org/install/>.

For more details and manual installation instructions, see
<https://lean-lang.org/install/manual/>.

In brief:

1. Install [VS Code](https://code.visualstudio.com/).
2. Install the official
   [Lean 4 VS Code extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4).
3. Open VS Code and follow the Lean extension's setup guide. If the guide does
   not open automatically, create a new empty file, click the `forall` symbol in
   the top-right corner of VS Code, and choose `Documentation > Docs: Show Setup
   Guide`.

## Downloading the Course Project

Use the Lean 4 VS Code extension's setup guide to download this existing
project.

1. Open the Lean setup guide in VS Code.
2. Choose **Download existing project**.
3. When asked for the project URL, paste:

   <https://github.com/fsefzig/lean_course_summer_26>

4. Choose a folder on your computer where the project should be saved.
5. Open the downloaded project folder in VS Code.

Make sure you open the whole project folder, not just one `.lean` file. When VS
Code opens the project, the Lean extension may ask to download or set up Lean
and the project dependencies. Accept these prompts. This project includes a
`lean-toolchain` file, so Lean will use the version expected for the course.
