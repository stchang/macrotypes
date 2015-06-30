extension hierarchy

A file extends its immediate parent file.

- stlc.rkt
   - stlc+lit.rkt
     - ext-stlc.rkt
       - stlc+tup.rkt
         - stlc+var.rkt
           - stlc+cons.rkt
             - stlc+box.rkt
           - stlc+rec-iso.rkt
     - stlc+sub.rkt
       - stlc+rec+sub.rkt (also pull in tup from stlc+var.rkt)
     - sysf.rkt
       - fomega.rkt
       - fomega2.rkt