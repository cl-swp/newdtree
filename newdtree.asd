(in-package :asdf)

(defsystem "newdtree"
  :description "newdtree: A new version of dtree (see, 'Paradigms of Artificial Intelligence Programming' by Peter Norvig"
  :version "0.0.1"
  :author "Seiji Koide <koide@ontolonomy.co.jp>"
  :licence "PAIP"
  :components ((:file "packages")
               (:file "utilities")
               (:file "newdtree")))
