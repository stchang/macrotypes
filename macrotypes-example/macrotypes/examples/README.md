extension hierarchy

A file extends its immediate parent file.

- stlc.rkt
   - stlc+lit.rkt
     - ext-stlc.rkt
       - stlc+tup.rkt
         - stlc+reco+var.rkt
           - stlc+cons.rkt
             - stlc+box.rkt
           - exist.rkt (and type=? from stlc+rec-iso)
         - stlc+rec-iso.rkt (and variants from stlc+reco+var)
     - stlc+sub.rkt
       - stlc+reco+sub.rkt (also pull in tup from stlc+reco+var.rkt)
     - sysf.rkt
       - fsub.rkt (also stlc+reco+sub)
       - fomega.rkt
         - fomega3.rkt
       - fomega2.rkt