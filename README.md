## agda-fresh

This repository collects some resources and notes that I found helpful when
getting started with Agda.

[The main GitHub repository for the Agda programming language is github.com/agda/agda.](https://github.com/agda/agda)

### Courses
The courses subdirectory contains instructional materials and Agda source code
from some classes and tutorials on Agda and dependent type theory.

### Installation
I'm using Ubuntu 14.04, so at first I tried the default agda-mode package,
installed with

    apt-get agda-mode

This was working fine until I started using resources from other developers
(namely, Ulf Norell's agda-prelude repository).

I found that trying to use the Ubuntu package along with packages from others
who installed Agda with cabal was generally a disaster.  There's no reason
things should be this difficult, and there are probably ways to sort out the
mess, but I wanted to save time and keep things simple, so I switched to
the cabal installation of Agda. This requires the following steps:

1. Removed the default Ubuntu packages:

    sudo apt-get remove happy

2. Install Agda using the method described here:

   http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Cabal.Linux

   Specifically, do the following (but see caveats below):

        sudo apt-get install zliblg-dev libncurses5-dev cabal-install emacs ghc6 haskell-mode
    	cat 'PATH=$PATH:~/.cabal/bin' >> ~/.bashrc
    	source ~/.bashrc
    	cabal update
    	cabal install happy alex haskell-src-exts Agda
    	agda-mode setup

   **Caveats**: If you already have a recent or custom version of one of the
   packages listed after `sudo apt-get install` above (like emacs), then you may
   want to leave this package out of the `sudo apt-get install` command.
   If you have a custom or non-standard emacs configuration, you probably want
   to skip the last step, `agda-mode setup,` because it merely modifies your
   `.emacs` file by adding the lines: 

        (load-file (let ((coding-system-for-read 'utf-8))
                        (shell-command-to-string "agda-mode locate")))

   You can add these lines yourself to whatever emacs config file you use for
   such customizations.

3. Clone the Agda standard library, [agda-stdlib](https://github.com/agda/agda-stdlib)
   to your local drive, then call `cabal install` from inside the
   `agda-stdlib/ffi` directory of the cloned repository:

        mkdir -p ~/git/AGDA
        cd ~/git/AGDA
        git clone git@github.com:agda/agda-stdlib.git
		cd agda-stdlib/ffi
		cabal install

4. Add the following line to your custom emacs file:

        '(agda2-include-dirs (quote ("." "/home/williamdemeo/git/AGDA/agda-stdlib/src" "/usr/share/agda-stdlib")))


### Troubleshooting

1. **Installation problems** When trying to install Agda with cabal, I got the
   following error message:
   
        The program cpphs version >=1.18.6 && <1.19 is required

   So I installed a newer version of cpphs as follows:

        cabal install cpphs-1.18.9

   This enabled me to install Agda, but then some Agda code from a few years ago
   wouldn't parse because of the changes to the standard library.  I had to
   upgrade Agda again, and this resulted in the same error:

        The program cpphs version >=1.18.6 && <1.19 is required

   The following worked:

        cabal install cpphs-1.19
        cabal install Agda

2. **Unicode problems** After Agda was finally installed, I had a terrible time
   getting unicode fonts to appear as expected.  (Personally, I would simply
   avoid the hassle of getting unicode working and just use plain ascii
   text. However, lots of Agda developers use unicode, and we want their source
   files to appear correctly in Emacs, so it's important to get unicode working
   properly. I found the following solution: 

   - Install the `ttf-bitstream-vera` font package:

            sudo apt-get install ttf-bitstream-vera

   - Add the following lines to your emacs customization file (e.g. `.emacs`):

            (load-file (let ((coding-system-for-read 'utf-8))
                            (shell-command-to-string "agda-mode locate")))
            (set-fontset-font "fontset-default" 'unicode "DejaVu Sans")

   (If you already have the first two of these lines, just add the third!)
   

### Summary of Emacs keybindings for Agda

-------------------------

-- Writing definitions interactively

-- Add a question mark and then type C-c C-l to create a hole.

-- Type C-c C-f to move into the next hole.

-- Type C-c C-c to be prompted for what goes in the hole.

-- Type m to split on the variable in the hole.

-- Type C-c C-f to move into the next hole.

-- Type C-c C-, to get the type required in the current hole.

-- Enter an appropriate object in the hole and type C-c C-space to remove the hole.

{- SUMMARY
   ? then C-c C-l creates hole
   C-c C-f moves to next hole
   C-c C-c prompts for what goes in hole
   m splits on variable in hole
   C-c C-, in hole gets type required
   C-c C-space removes hole
-}


