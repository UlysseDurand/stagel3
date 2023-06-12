(TeX-add-style-hook
 "tikzit"
 (lambda ()
   (TeX-run-style-hooks
    "tikz")
   (TeX-add-symbols
    '("ctikzfig" 1)
    '("tikzfig" 1)))
 :latex)

