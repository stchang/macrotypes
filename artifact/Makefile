all:
	git archive --prefix=popl2017-artifact/ --remote=../ -o popl2017-artifact.tar popl2017-artifact
	packer build artifact.json

32-bit:
	git archive --prefix=popl2017-artifact/ --remote=../ -o popl2017-artifact.tar popl2017-artifact
	packer build artifact-32.json

readme:
	scribble +m --html README.scrbl

clean:
	rm -rf output-virtualbox-iso
	rm README.html
	rm manual-fonts.css
	rm manual-racket.css
	rm manual-racket.js
	rm manual-style.css
	rm scribble-common.js
	rm scribble.css
