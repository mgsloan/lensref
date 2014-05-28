
Introduction.pdf: Introduction.pandoc dotplugin
	pandoc -N -f markdown+lhs -t latex --filter ./dotplugin $< -o $@

dotplugin: DotPlugin.hs
	ghc --make $< -o $@


