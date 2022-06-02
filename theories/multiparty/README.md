# ICFP 2022 Artifact

Name: "Multiparty GV: Functional Multiparty Session Types With Certified Deadlock Freedom."

## Artifact Instructions

This is the Coq development of MPGV.
This development proves the main theorems that MPGV satisfies:
- Global progress
- Deadlock freedom
- Full reachability (memory leak freedom)

The files of interest are in `theories/multiparty/*.v`:
- langdef.v: Definition of the MPGV language (syntax + operational semantics + type system).
- globaltypes.v: The definition of global types, and proof that global type consistency implies coinductive consistency.
- binary.v: Encoding binary session types in MPGV.
- definitions.v: Definitions required to formulate the main theorems (mainly, definition of deadlock freedom and full reachability).
- theorems.v: The proofs of the main theorems (global progress, deadlock freedom, and full reachability).

The correspondence between these files and the paper is as follows:
- langdef.v: Section 3
- globaltypes.v: Section 3.2.
- binary.v: Section 4
- definitions.v: First half of section 5 (the definitions)
- theorems.v: Second half of section 5 (the theorems)
The files themselves contain further comments on the precise correspondence to the numbered definitions and theorems in the paper.

The other files in the `theories/multiparty/*.v` folder contain internal details of the proofs.
These files are checked by Coq and hence need not be checked to verify the correctness of the theorems.
- rtypesystem.v: Run-time type system of MPGV.
- invariant.v: Definition of the configuration invariant and various lemmas about it.
- progress.v: Lemmas showing that the invariant implies strong progress. These lemmas are used by theorems.v.
- ycombinator.v: Definition of the y-combinator that can be used to build recursive functions.
- mutil.v: Various utilities and imports.

### Build instructions

The VM already has the required dependencies installed, and you can simply run `make`.
This will make Coq check all the theorems in the development.

To build the development from source, install the following dependencies:

* Coq (we tested with Coq 8.15.1)
* std++ (we tested with dev.2022-05-16.1.411eb445)
* Iris (we tested with dev.2022-05-25.0.d46e4472)

We recommend installing the `opam` package manager and then installing the `coq-iris` package as follows.
This was done as follows for the VM:

    sudo apt-get install opam
    opam init
    eval $(opam env)
    opam repo add coq-released https://coq.inria.fr/opam/released
    sudo apt-get libgmp-dev
    opam install coq-iris

This will install the required dependencies.
Depending on your platform, you may need to install opam in a different way, see https://opam.ocaml.org/ for details.

You can then compile this project with `make`.

### Difference between the paper and Coq

The Coq development is slightly more general than the paper.
In Coq, we first define a coinductive consistency relation (called [consistent] in Coq).
We then prove that this implies the consistency notion used in the paper (called [consistent_gt] in Coq), which uses global types.
This is stronger than what is in the paper, because we can potentially type check more programs using [consistent] than with [consistent_gt].
The reviewers asked for this change, and in the final version of the paper we will also use these two notions of consistency, like we already do in Coq.


## QEMU Instructions

The ICFP 2022 Artifact Evaluation Process is using a Debian QEMU image as a
base for artifacts. The Artifact Evaluation Committee (AEC) will verify that
this image works on their own machines before distributing it to authors.
Authors are encouraged to extend the provided image instead of creating their
own. If it is not practical for authors to use the provided image then please
contact the AEC co-chairs before submission.

QEMU is a hosted virtual machine monitor that can emulate a host processor
via dynamic binary translation. On common host platforms QEMU can also use
a host provided virtualization layer, which is faster than dynamic binary
translation.

QEMU homepage: https://www.qemu.org/

### Installation

#### OSX
``brew install qemu``

#### Debian and Ubuntu Linux
``apt-get install qemu-kvm``

On x86 laptops and server machines you may need to enable the
"Intel Virtualization Technology" setting in your BIOS, as some manufacturers
leave this disabled by default. See Debugging.md for details.


#### Arch Linux

``pacman -Sy qemu``

See the [Arch wiki](https://wiki.archlinux.org/title/QEMU) for more info.

See Debugging.md if you have problems logging into the artifact via SSH.


#### Windows 10

Download and install QEMU via the links at

https://www.qemu.org/download/#windows.

Ensure that `qemu-system-x86_64.exe` is in your path.

Start Bar -> Search -> "Windows Features"
          -> enable "Hyper-V" and "Windows Hypervisor Platform".

Restart your computer.

#### Windows 8

See Debugging.md for Windows 8 install instructions.

### Startup

The base artifact provides a `start.sh` script to start the VM on unix-like
systems and `start.bat` for Windows. Running this script will open a graphical
console on the host machine, and create a virtualized network interface.
On Linux you may need to run with `sudo` to start the VM. If the VM does not
start then check `Debugging.md`

Once the VM has started you can login to the guest system from the host.
Whenever you are asked for a password, the answer is `password`. The default
username is `artifact`.

```
$ ssh -p 5555 artifact@localhost
```

You can also copy files to and from the host using scp.

```
$ scp -P 5555 artifact@localhost:somefile .
```

### Shutdown

To shutdown the guest system cleanly, login to it via ssh and use

```
$ sudo shutdown now
```

### Artifact Preparation

Authors should install software dependencies into the VM image as needed,
preferably via the standard Debian package manager. For example, to install
GHC and cabal-install, login to the host and type:

```
$ sudo apt update
$ sudo apt install ghc
$ sudo apt install cabal-install
```

If you really need a GUI then you can install X as follows, but we prefer
console-only artifacts whenever possible.

```
$ sudo apt install xorg
$ sudo apt install xfce4   # or some other window manager
$ startx
```

See Debugging.md for advice on resolving other potential problems.

If your artifact needs lots of memory you may need to increase the value
of the `QEMU_MEM_MB` variable in the `start.sh` script.

When preparing your artifact, please also follow the [Submission
Guidelines](https://icfp22.sigplan.org/track/icfp-2022-artifact-evaluation#Submission-Guidelines).
