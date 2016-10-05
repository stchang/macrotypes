artifact: Type Systems as Macros
===

This is the source code for the artifact for "Type Systems as Macros".

To build the artifact:
- Install [packer](https://www.packer.io), [Racket](https://racket-lang.org),
  and [VirtualBox](https://www.virtualbox.org/wiki/Downloads).
- Run `make`. You should have a new folder `./output-virtualbox-iso/` that
  contains a `.ovf` and `.vmdk` file. Building the image takes approximately 1 hour.
- Open VirtualBox, click `File -> Import Appliance`, then navigate to the
  `.ovf` file.
- We recommend creating the VM with 2GB of RAM.

Inside the VM, the Desktop folder will have a copy of the POPL 2017 paper, a
shortcut to the DrRacket IDE, and a `README.html` with detailed instructions.

VM username: `artifact`

VM password: `artifact`
