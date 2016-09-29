#!/usr/bin/env bash

# Setup script for POPL 2017 artifact, "Type Systems as Macros" (32-bit version)

## -----------------------------------------------------------------------------
# Global variables

RKT_INSTALLER="racket-6.6-i386-linux.sh"
ARTIFACT="popl2017-artifact"
ARTIFACT_TAR="${ARTIFACT}.tar"
PAPER_TITLE="type-systems-as-macros"
DESKTOP="/home/artifact/Desktop"

## -----------------------------------------------------------------------------
# Fundamentals

# Make sure there is a Desktop
mkdir -p ~/Desktop

# Installing vagrant keys
mkdir ~/.ssh
chmod 700 ~/.ssh
cd ~/.ssh
wget --no-check-certificate 'https://raw.github.com/mitchellh/vagrant/master/keys/vagrant.pub' -O authorized_keys
chmod 600 ~/.ssh/authorized_keys
chown -R artifact ~/.ssh

## -----------------------------------------------------------------------------
# Install Racket

cd ~
# first download Racket v6.6
wget http://mirror.racket-lang.org/installers/6.6/${RKT_INSTALLER}
# Do a local install. A unix-style install is preferable in some ways, but the
# permissions are a pain when overriding packages
sh ${RKT_INSTALLER} --in-place --dest ~/racket
# Add racket to the path
export PATH=~/racket/bin:$PATH
echo "export PATH=~/racket/bin:$PATH" >> ~/.bashrc
# setup, but don't build the docs (to save memory)
raco setup -D

## -----------------------------------------------------------------------------
# Set up the artifact files

tar -xf ${ARTIFACT_TAR}
rm ${ARTIFACT_TAR}
cd ~/${ARTIFACT}
raco pkg install --deps search-auto ../${ARTIFACT}
cd ./artifact
make readme
mkdir -p ${DESKTOP}
ln -s `pwd`/README.html ${DESKTOP}/README.html
ln -s `pwd`/paper.pdf ${DESKTOP}/${PAPER_TITLE}.pdf
cd ${DESKTOP}

## -----------------------------------------------------------------------------
# Configure XFCE, instead of directly configuring this put it in the
# .bash_profile because the command won't work without X11 running.

# Put in .profile because .xsessionrc isn't run by lightdm sometimes
echo "xfconf-query -c xsettings -p /Net/ThemeName -s Xfce" >> ~/.profile
echo "xfconf-query -c xsettings -p /Net/IconThemeName -s Humanity" >> ~/.profile

# Install an .xsession
echo "source .profile"  > ~/.xsession
echo "startxfce4"      >> ~/.xsession

# Create a desktop shortcut for DrRacket
echo "[Desktop Entry]"             > ${DESKTOP}/DrRacket.desktop
echo "Version=1.0"                >> ${DESKTOP}/DrRacket.desktop
echo "Type=Application"           >> ${DESKTOP}/DrRacket.desktop
echo "Name=DrRacket"              >> ${DESKTOP}/DrRacket.desktop
echo "Comment="                   >> ${DESKTOP}/DrRacket.desktop
echo "Exec=/home/artifact/racket/bin/drracket" >> ${DESKTOP}/DrRacket.desktop
echo "Icon=/home/artifact/racket/share/drracket-exe-icon.png" >> ${DESKTOP}/DrRacket.desktop
echo "Path="                      >> ${DESKTOP}/DrRacket.desktop
echo "Terminal=false"             >> ${DESKTOP}/DrRacket.desktop
echo "StartupNotify=false"        >> ${DESKTOP}/DrRacket.desktop

chmod +x ${DESKTOP}/DrRacket.desktop

# Center wallpaper and set bg color
echo "xfconf-query -n -t int -c xfce4-desktop -p /backdrop/screen0/monitorVBOX0/workspace0/image-style -s 1" >> ~/.profile
echo "xfconf-query -n -t uint -t uint -t uint -t uint -c xfce4-desktop -p /backdrop/screen0/monitorVBOX0/workspace0/color1 -s 65535 -s 65535 -s 65535 -s 65535" >> ~/.profile

# Setup vimrc
echo "set background=dark" >> ~/.vimrc
echo "set nu" >> ~/.vimrc
echo "set ruler" >> ~/.vimrc

## -----------------------------------------------------------------------------
# Cleanup
rm ~/${RKT_INSTALLER}
