extension hierarchy

A file extends its immediate parent file.

- stlc.rkt
   - stlc+lit.rkt
     - ext-stlc.rkt
       - stlc+tup.rkt
         - stlc+var.rkt
           - stlc+cons.rkt
             - stlc+box.rkt
     - stlc+sub.rkt
       - stlc+rec+sub.rkt (also pull in tup from stlc+var.rkt)
     - sysf.rkt