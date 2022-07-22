# ICFP 2022 Artifact

Name: "Multiparty GV: Functional Multiparty Session Types With Certified Deadlock Freedom."

## Artifact Instructions

This is the Coq development of MPGV.
This development proves the main theorems that MPGV satisfies:
- Global progress
- Deadlock freedom
- Full reachability (memory leak freedom)

The files of interest are in `theories/multiparty/*.v`:
- paper_annotated.pdf: a version of the paper annotated with references to the Coq sources for the definitions, lemmas, and theorems.
- langdef.v: Definition of the MPGV language (syntax + operational semantics + type system).
- globaltypes.v: The definition of global types, and proof that global type consistency implies coinductive consistency.
- binary.v: Encoding binary session types in MPGV.
- definitions.v: Definitions required to formulate the main theorems (mainly, definition of deadlock freedom and full reachability).
- theorems.v: The proofs of the main theorems (global progress, deadlock freedom, and full reachability).

The correspondence between these files and the paper is as follows:
- langdef.v: Section 3
- binary.v: Section 4
- definitions.v: First half of section 5 (the definitions)
- theorems.v: Second half of section 5 (the theorems)
- globaltypes.v: Section 6.
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

To build the code, install the opam package manager, and then execute the following in the root folder:

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam install .

Alternatively, install the following dependencies:
* Coq
* std++
* Iris
(see cgraphs.opam for versions)

These can be installed by running:

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam install coq-iris

You can then compile this project with `make`.

We recommend installing the `opam` package manager and then installing the `coq-iris` package as follows.
For Linux distributions with `apt`, the following script performs all the steps:

    sudo apt-get install opam
    opam init
    eval $(opam env)
    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
    sudo apt-get libgmp-dev
    opam install coq-iris
    make

Depending on your platform, you may need to install opam in a different way, see https://opam.ocaml.org/ for details.

### Axioms

*Classical logic*

We use classical logic.
Strictly speaking, classical axioms should not be necessary.
The reason is that the final theorems we are proving are all decidable.
For instance, it should be decidable whether a given configuration can take a step or not.
One could decide this by checking if any of the operational semantics rules apply to the configuration.
If the conclusion of a theorem is decidable, then use of the excluded middle in the proof can be avoided.
However, actually doing this in Coq would require making a lot of changes, so we use classical logic for convenience.

*Functional extensionality*

We use the axiom of functional extensionality.
Coq's default notion of equality for functions is syntactic.
For the proofs it is convenient to use mathematical equality of functions.

*Coinductive extensionality*

Coq's default notion of equality is not good enough for coinductive types:
the default equality is syntactic equality and not extensional equality.
We add an axiom to make equality extensional.
See https://coq.inria.fr/refman/language/core/coinductive.html:
"More generally, as in the case of positive coinductive types,
it is consistent to further identify extensional equality of coinductive
types with propositional equality"
Such an axiom is similar to functional extensionality, but for coinductive types.

These extensionality axioms could be avoided by working up to an appropriate equivalence relation.
However, doing this in Coq is quite inconvenient, so we add them as an axiom.
In future proof assistants, perhaps based on observational type theory or HoTT,
one would not need these extensionality axioms if they are provable.


### Dependencies

We depend on stdpp and Iris. Stdpp offers a more comprehensive standard library for Coq. From Iris we mainly use the Iris proof mode.
We also use a modified version of Iris' uPred -- whereas Iris' uPred is affine, our uPred is linear.

We depend on the connectivity graph library of Jacobs et al. [https://doi.org/10.1145/3498662].
This library provides tools to prove deadlock freedom for languages where this property follows from the acyclic reference structure of the configuration.
In particular, the library provides tools for showing that the configuration maintains the acyclicity invariant under stepping in the operational semantics, and it provides an induction principle for acyclic graphs using which we prove full reachability.


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
