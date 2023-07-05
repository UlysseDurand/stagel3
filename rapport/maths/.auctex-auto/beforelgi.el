(TeX-add-style-hook
 "beforelgi"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("inputenc" "utf8") ("biblatex" "style=numeric") ("changebar" "xcolor" "leftbars")))
   (add-to-list 'LaTeX-verbatim-environments-local "lstlisting")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "lstinline")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "url")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "nolinkurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperbaseurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperimage")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "href")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "lstinline")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "path")
   (TeX-run-style-hooks
    "inputenc"
    "amssymb"
    "biblatex"
    "amsmath"
    "xcolor"
    "enumitem"
    "tikz"
    "tikzit"
    "bbold"
    "changebar"
    "listings"
    "hyperref")
   (TeX-add-symbols
    '("norm" 1))
   (LaTeX-add-environments
    '("answer" 1)
    "myindentpar")
   (LaTeX-add-bibliographies
    "bib")
   (LaTeX-add-lengths
    "mydepth"
    "myheight")
   (LaTeX-add-saveboxes
    "mybox")
   (LaTeX-add-xcolor-definecolors
    "DarkBlue"))
 :latex)

