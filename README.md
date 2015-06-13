## Agda

This repository collects some resources and notes that I found helpful when
getting started with Agda.

### Installation
At first I used `apt-get` to install the package `agda-mode`.  This seemed to
work fine for a while, until I started using resources from other developers
(like Ulf Norell's agda-prelude repository).

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

### Troubleshooting

When trying to install Agda with cabal, I got the following error message:
"The program cpphs version >=1.18.6 && <1.19 is required"
So I installed a newer version of cpphs as follows:

    cabal install cpphs-1.18.9

After Agda was finally installed, I had a terrible time getting unicode fonts to
appear as expected.  (Personally, I would simply avoid the hassle of getting
unicode working and just use plain ascii text. However, lots of Agda developers
use unicode, and we want their source files to appear correctly in Emacs, so
it's important to get unicode working properly. I found the following solution:

1. Install the `ttf-bitstream-vera` font package:

        sudo apt-get install ttf-bitstream-vera

2. Add the following lines to your emacs customization file (e.g. `.emacs`):

        (load-file (let ((coding-system-for-read 'utf-8))
                        (shell-command-to-string "agda-mode locate")))
        (set-fontset-font "fontset-default" 'unicode "DejaVu Sans")

   (If you already have the first two of these lines, just add the third!)
   
