(TeX-add-style-hook
 "beforelgi"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("inputenc" "utf8") ("changebar" "xcolor" "leftbars")))
   (add-to-list 'LaTeX-verbatim-environments-local "lstlisting")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "href")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperimage")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperbaseurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "nolinkurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "url")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "lstinline")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "lstinline")
   (TeX-run-style-hooks
    "inputenc"
    "amssymb"
    "amsmath"
    "xcolor"
    "enumitem"
    "bbold"
    "changebar"
    "listings"
    "hyperref")
   (TeX-add-symbols
    '("norm" 1))
   (LaTeX-add-environments
    "myindentpar"
    "answer")
   (LaTeX-add-lengths
    "mydepth"
    "myheight")
   (LaTeX-add-saveboxes
    "mybox")
   (LaTeX-add-xcolor-definecolors
    "DarkBlue"))
 :latex)

