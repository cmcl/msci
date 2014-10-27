;; Work around an (apparent) bug in Proof General in which it
;; doesn't properly understand _CoqProject arguments for coqtop.
((coq-mode .
	   ((coq-load-path . (("/home/craig/projects/msci/Coq Developments/msci" "MSciProject")
			      ("/home/craig/projects/msci/Coq Developments/msci/Metatheory" "MSciProject.Metatheory"))))))
