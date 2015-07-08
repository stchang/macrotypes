extension hierarchy

A file extends its immediate parent file.

- stlc.rkt
   - stlc+lit.rkt
     - ext-stlc.rkt
       - stlc+tup.rkt
         - stlc+reco+var.rkt
           - stlc+cons.rkt
             - stlc+box.rkt
           - stlc+rec-iso.rkt
           - exist.rkt
     - stlc+sub.rkt
       - stlc+reco+sub.rkt (also pull in tup from stlc+reco+var.rkt)
     - sysf.rkt
       - fomega.rkt
       - fomega2.rkt