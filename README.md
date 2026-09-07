# Brown CS 1715: Formal Proof and Verification, 2026

In this repository, you'll find Lean files for [CS1715](https://browncs1715.github.io/).

## Using this repository

This repository is a [Lean project](https://leanprover-community.github.io/install/project.html). There are some basic steps you should take at the beginning to set it up. These only need to be done once.

### Setup

We assume that you have installed:

- `git`
- `lean` (via `elan`)
- VSCode and the Lean extension

following our [course setup instructions](https://browncs1715.github.io/setup.html).

To set up this project, run:

```bash
git clone https://github.com/BrownCS1715/fpv2026.git
cd fpv2026
lake exe cache get
lake build LoVe.LoVelib
```

When you open VSCode, make sure that you use the **Open Folder** feature
to open the entire `fpv2026` directory,
instead of opening individual files.
The easiest way to do this is from the command line:

```bash
cd fpv2026
code .
```

But `File -> Open Folder...` works fine too.

### Codespaces setup

If you are using GitHub Codespaces for this class, you can ignore all of the above. Open your codespace and get to work; all of these setup steps are done for you!

### Pulling changes

We will add files to this repository as the course progresses,
and occasionally edit old files. We will try very hard to make the homework assignments "read-only": once they are posted, we will not modify them, and will announce if we do.

You can check whether you have modified any files in the repository with

```bash
git status
```

If you have no modified files, pulling our updates is easy:

```bash
git pull
```

If you have modifications, you should either commit them:

```bash
git commit -am "your message here"
git pull
```

or stash them:

```bash
git stash
git pull
git stash pop
```

Note that modifying files could potentially lead to merge conflicts.
For this reason, especially with the homeworks, we recommend editing a copy of the files:

```bash
cp ./Homework/Homework_1.lean ./Homework/Homework_1_rob.lean
```

I would complete the homework in the copy, `Homework_1_rob.lean`, and submit that file on Gradescope.

### Forking this repository

If you are comfortable with `git`, you may want to push your work to your own copy of this repository as a backup. This is a wise idea! However, your work will probably contain solutions to homework assignments that shouldn't be shared publicly, and GitHub enforces that forks of a public repository must also be public.

Instead of using the built-in "Fork" button on GitHub, we ask that you do this the old fashioned way. (Replace `{username}` below with your GitHub user name.)

- Clone this repository locally or in Codespaces as above.
- Create a new, empty, private GitHub repository under your account, also called `fpv2026`.
- In the root of your clone of this repo, run `git remote add {username} git@github.com:{username}/fpv2026.git`
- You can now `git pull` to get updates from our repository, and `git push username main` to push commits to the `main` branch of your new private fork.

<details>
<summary>Why not GitHub Classrooms?</summary>

The astute reader will notice that this workaround is doing something similar to what GitHub Classrooms can achieve. We've decided to keep things simple and avoid some of the overhead involved with a Classrooms setup. In particular, it seems that with the new Classrooms infrastructure introduced this spring, you all would receive pull requests every time we update our version of the repo, which feels too loud!

</details>

### Debugging

The Lean files should be quick to load.
If you see orange bars in VSCode for a long time (20 seconds is way too much),
something might be wrong.
This can be caused by accidentally making changes to library files,
or by having too many files open in VSCode that import each other.

First, in VSCode, close any editor tabs that you aren't using anymore.
Then open the Command Palette (`ctrl-shift-p` or `cmd-shift-p`)
and run `Lean 4: Restart Server`.

If that doesn't work, let's make sure you have a fresh copy of the library.
In the root `fpv2026` directory, run:

```bash
lake update
lake exe cache get
lake build LoVe.LoVelib
```

If this last line takes more than a few seconds, things might still be wrong.
Talk to Rob or the TAs.

## Contents

`LoVe/LoVelib.lean` is a mini-library that we will use for this class.

### Lecture notes

We are following the text _The Hitchhiker's Guide to Logical Verification_.
Corresponding to each chapter of the text, there is a `.lean` file that we will work through in class.
These files are posted here in the `Lectures` folder.

### Exercises

The files in the `Exercises` folder are "homework-like" problems for extra practice. There will be an optional weekly lab session to work on these exercises. The labs aren't required, but are great practice for the homeworks, a good opportunity to make up the difference between the theory in lectures and the practice on assignments. These lab sessions will be collaborative. Solutions to the exercises will be posted.

### Homework assignments

There is approximately one homework assignment per chapter of the Hitchhiker's Guide. These will be posted on or before the day of the corresponding lecture, and will be due after the following week's lecture. You may discuss problems with your classmates, but the work you submit must be your own. We recommend the "clean blackboard" method: after discussing the problem, erase your blackboard/editor window/etc, and write up the solutions individually. Homeworks will be posted in the `Homework` folder.
