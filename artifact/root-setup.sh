#!/usr/bin/env bash

# Dependencies
sudo apt-get update -y -qq > /dev/null

# Install guest additions/Vagrant NFS
sudo apt-get -y -q install linux-headers-$(uname -r) build-essential dkms nfs-common
sudo apt-get -y -q install virtualbox-guest-utils virtualbox-guest-x11 virtualbox-guest-dkms

# Install necessary packages
sudo apt-get -y -q install firefox vim xvfb git wget tar xfce4 lightdm mupdf ack-grep
# Install latex, for Scribble
sudo apt-get -y -q --no-install-recommends install texlive-latex-base texlive-fonts-recommended texlive-fonts-extra texlive-latex-extra pgf tex-gyre

# Add an XSession session for lightdm
sudo echo "[Desktop Entry]"         > /usr/share/xsessions/custom.desktop
sudo echo "Name=Xsession"          >> /usr/share/xsessions/custom.desktop
sudo echo "Exec=/etc/X11/Xsession" >> /usr/share/xsessions/custom.desktop

# Configure lightdm auto-login
sudo echo "[SeatDefaults]"           >> /etc/lightdm/lightdm.conf
sudo echo "user-session=custom"      >> /etc/lightdm/lightdm.conf
sudo echo "autologin-user=artifact"  >> /etc/lightdm/lightdm.conf
sudo echo "autologin-user-timeout=0" >> /etc/lightdm/lightdm.conf

# Setup sudo to allow no-password sudo for "sudo"
cp /etc/sudoers /etc/sudoers.orig
sed -i -e '/Defaults\s\+env_reset/a Defaults\texempt_group=sudo' /etc/sudoers
sed -i -e 's/%sudo ALL=(ALL) ALL/%sudo ALL=NOPASSWD:ALL/g' /etc/sudoers

# Install wallpaper
wget -O /usr/share/backgrounds/xfce/xfce-blue.jpg http://ccs.neu.edu/home/stchang/popl2017/logo.png
