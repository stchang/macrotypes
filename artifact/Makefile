all:
	git archive --prefix=popl2017-artifact/ --remote=../ -o popl2017-artifact.tar popl2017-artifact
	packer build artifact.json

32-bit:
	git archive --prefix=popl2017-artifact/ --remote=../ -o popl2017-artifact.tar popl2017-artifact
	packer build artifact-32.json

readme:
	scribble +m --htmls README.scrbl

clean:
	rm -rf output-virtualbox-iso
