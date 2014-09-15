{
open Printf
open List
}

let id = ['a'-'z' 'A'-'Z' '_']['a'-'z' 'A'-'Z' '0'-'9' '_']*
let space = [' ' '\t' '\n']+

(* the rule for processing keywords "Lemma" or "Theorem" *)
rule theorem res = parse
	| "Lemma" { name res lexbuf }
	| "Theorem" { name res lexbuf }
	| "Corollary" { name res lexbuf }
	| eof { res }
	| "(*" { comment_thm res lexbuf }
	| _ { theorem res lexbuf }
(* the rule for processing the name of the current lemma(or theorem) *)
and name res = parse
	| id as ident { name' ident res lexbuf }
	| "(*" { comment_name res lexbuf }
  | space { name res lexbuf }  
and name' ident res = parse
	| ':' { eater ident res lexbuf }
	| "(*" { comment_name' ident res lexbuf }
	| _ { eater ident res lexbuf }
(* the rule for processing the definition of the current lemma(or theorem)  *)
and eater ident res = parse
	| '.' { proof_body ident 0 res lexbuf }
	| "(*" { comment_eater ident res lexbuf }
	| _ { eater ident res lexbuf  }
(* the rule for counting the number of tactics of the current lemma(or theorem)  *)
and proof_body ident n res = parse
	| "Proof." { proof_body ident n res lexbuf }
	| "Qed." { theorem ((ident, n) :: res) lexbuf }
	| "(*" { comment_proof ident n res lexbuf }
	| id as cur 
		{ 
			let tac_list = [
			"abtract";
			"absurd";
			"admit";
			"apply";
			"assert";
			"assumption";
			"auto";
			"autorewrite";
			"autounfold";
			"case";
			"case_eq";
			"cbv";
			"change";
			"classical_left";
			"classical_right";
			(* "clear"; *)
			"clearbody";
			"cofix";
			"compare";
			"compute";
			"congruence";
			"constr_eq";
			"constructor";
			"contradict";
			"contradiction";
			"cut";
			"cutrewrite";
			"decide";
			"decompose";
			"destruct";
			"discriminate";
			"discrR";
			"do";
			"eapply";
			"eassumption";
			"eauto";
			"ecase";
			"econstructor";
			"edestruct";
			"ediscriminate";
			"eelim";
			"eexact";
			"eexists";
			"einduction";
			"einjection";
			"eleft";
			"elim";
			"elimtype";
			"erewrite";
			"eright";
			"esimplify_eq";
			"esplit";
			"evar";
			"exact";
			"exfalso";
			"exists";
			"f_equal";
			"fail";
			"field";
			"field_simplify";
			"field_simplify_eq";
			"first";
			"firstorder";
			"fix";
			"fold";
			"fourier";
			"generalize";
			"has_evar";
			"hnf";
			"idtac";
			"induction";
			"info";
			"injection";
			"instantiate";
			"intro";
			"intros";
			"intuition";
			"inversion";
			"inversion_clear";
			"inversion_cleardots";
			"is_evar";
			"lapply";
			"lazy";
			"left";
			"lia";
			"move";
			"nsatz";
			"omega";
			"pattern";
			"pose";
			"progress";
			"psatz";
			"quote";
			"red";
			"refine";
			"reflexivity";
			"remember";
			"rename";
			"repeat";
			"replace";
			"revert";
			"rewrite";
			"right";
			"ring";
			"ring_simplify";
			"rtauto";
			"set";
			"setoid_replace";
			"simpl";
			"simple";
			"simplify_eq";
			"solve";
			"specialize";
			"split";
			"split_Rabs";
			"split_Rmult";
			"stepl";
			"stepr";
			"subst";
			"symmetry";
			"tauto";
			"transitivity";
			"trivial";
			"try";
			"unfold";
			"vm_compute";
			"case_var";
			"destruct_notin";
			"gather_vars";
			"pick_fresh";
			"get_env";
			"unsimpl_map_bind";
			"gather_atoms";
			"case_nat";
			"build_result";
			"if_is_result";
			"_put";
			"_put2";
			"_put3";
			"_get";
			"_rem";
			"ltac_args";
			"nat_from_number";
			"dup_tactic";
			"get_head";
			"is_metavar";
			"false_inv_tactic";
			"app_darg";
			"app_arg";
			"app_assert";
			"app_evar";
			"build_app_alls";
			"build_app_args";
			"build_app_vars";
			"build_app_hyps";
			"boxerlist_next_type";
			"build_app_hnts";
			"build_app";
			"lets_build";
			"applys_build";
			"specializes_build";
			"introv_rec";
			"introv_to";
			"introv_base";
			"def_to_eq";
			"def_to_eq_sym";
			"asserts_rewrite_tactic";
			"cuts_rewrite_tactic";
			"rewrite_except";
			"unfolds_callback";
			"unfolds_base";
			"unfolds_in_base";
			"substs_below";
			"fequal_base";
			"fequal_post";
			"gen_until_mark";
			"intro_until_mark";
			"inverts_tactic";
			"injects_tactic";
			"case_if_on_tactic";
			"gen_eq_for_inductions";
			"apply_to_all_args";
			"intros_head_ltac_tag_subst";
			"inductions_post";
			"decides_equality_tactic";
			"splits_tactic";
			"unfold_goal_until_conjunction";
			"get_term_conjunction_arity";
			"get_goal_conjunction_arity";
			"destructs_conjunction_tactic";
			"branch_tactic";
			"unfold_goal_until_disjunction";
			"get_term_disjunction_arity";
			"get_goal_disjunction_arity";
			"destructs_disjunction_tactic";
			"get_term_existential_arity";
			"get_goal_existential_arity";
			"auto_tilde";
			"auto_star";
			"sort_tactic";
			"clears_tactic";
			"clear_last_base";
			"skip_with_existential";
			"skip_with_axiom";
			"gather_vars";
			"pick_fresh";
			"exists_fresh";
			"cross";
			"get_env";
			"unsimpl_map_bind";
			"simpl_list_hyp";
			"simpl_list_hyps";
			"skip";
			"contradictions";
			"cuts";
			"inversions";
			"poses";
			"puts";
			"asserts";
			"sets";
			"introz";
			"destructs";
			"env_fix_core";
			"env_fix";
			"binds_single";
			"binds_cases";
			"fresh_simpl_to_notin_in_context";
			"notin_solve_from";
			"notin_solve_from_context";
			"notin_solve_one";
			"notin_simpl";
			"notin_simpl_hyps";
			"notin_simpls";
			"notin_solve";
			"notin_contradiction";
			"notin_neq_solve";
			"fresh_solve_from";
			"fresh_solve_from_context";
			"fresh_solve_one";
			"fresh_simpl";
			"fresh_simpl_to_notin_in_goal";
			"fresh_simpl_to_notin_solve";
			"fresh_solve";
			"case_nat";
			"gather_vars_with";
			"beautify_fset";
			"pick_fresh_gen";
			"pick_freshes_gen";
			"test_pick_fresh_filter";
			"apply_fresh_base_simple";
			"apply_fresh_base";
			"pres";
			"pick_freshes";	
			"name_result";
			"show";
			"dup";
			"lets";
			"lets_simpl";
			"lets_hnf";
			"put";
			"applys";
			"applys_0";
			"applys_1";
			"applys_2";
			"applys_3";
			"applys_4";
			"applys_5";
			"applys_6";
			"applys_7";
			"applys_8";
			"applys_9";
			"applys_10";
			"applys_to";
			"applys_in";
			"applys_clear";
			"apply_clear";
			"constructors";
			"false_goal";
			"false";
			"tryfalse";
			"false_inv";
			"tryfalse_inv";
			"asserts";
			"cuts";
			"forwards";
			"specializes";
			"fapply";
			"sapply";
			"introv";
			"intros_all";
			"gen";
			"generalizes";
			"sets";
			"set_eq";
			"sets_eq";
			"ltac_pattern";
			"ltac_action_at";
			"protects";
			"rewrite_all";
			"asserts_rewrite";
			"cuts_rewrite";
			"rewrites";
			"replaces";
			"renames";
			"unfolds";
			"folds";
			"simpls";
			"unsimpl";
			"substs";
			"fequal";
			"fequals";
			"fequals_rec";
			"invert";
			"invert_tactic";
			"inverts";
			"inverts_tactic";
			"injects";
			"inject";
			"inversions";
			"injections";
			"case_if_on";
			"case_if";
			"gen_eq";
			"gen_eqs";
			"inductions";
			"induction_wf";
			"decides_equality";
			"splits";
			"splits_all";
			"destructs";
			"branch";
			"branches";
			"exists_original";
			"exists";
			"exists_";
			"auto";
			"f_equal";
			"constructor";
			"simple";
			"apply";
			"destruct";
			"induction";
			"inversion";
			"split";
			"subst";
			"right";
			"left";
			"rewrite";
			"subs";
			"sort";
			"clears";
			"clear_last";
			"skip";
			"skip_asserts";
			"skip_cuts";
			"skip_goal";
			"skip_rewrite";
			"skip_rewrite_all";
			"skip_induction";		
			"helper";
			"apply_fresh";
			"cross";
			"apply_empty_bis";
			"apply_empty";
			"unsimpl_map_bind";
			"folds";
			"unfolds";
			"unfold_hd";
			"simpls";
			"unsimpl";
			"rewrites";
			"asserts_rew";
			"do_rew";
			"do_rew_2";
			"gen_eq";
			"gen";
			"split3";
			"split4";
			"splits";
			"esplit2";
			"esplit3";
			"esplit4";
			"or_31";
			"or_32";
			"or_33";
			"destructi";
			"introv";
			"exists";
			"forward";
			"auto";
			"asserts";
			"apply";
			"contradictions";
			"destruct";
			"f_equal";
			"induction";
			"inversion";
			"inversions";
			"rewrite";
			"simpl";
			"split";
			"right";
			"left";
			"subst";
			"use";
			"simpl_env";
			"binds_get";
			"binds_case";
			"apply_ih_bind";
			"apply_ih_map_bind";
			"case_nat";
			"case_var";
			"inst_notin";
			"pick_fresh";
			"pick_freshes";	
			"typ_cases";
			"exp_cases";
			"type_cases";
			"expr_cases";
			"wf_typ_cases";
			"wf_env_cases";
			"wf_lenv_cases";
			"lenv_split_cases";
			"value_cases";
			"red_cases";
			"typing_cases";
			"pick";
      "decEq";
      "omegaContradiction";
      "caseEq";
      "analyze_binds_uniq";
      "fsetdec";
      "rewrite_env";
      "solve_notin";
      "Simplify";
      "Destruct";
			] in
			if(mem cur tac_list) then
				proof_body ident (n + 1) res lexbuf
			else
				proof_body ident n res lexbuf
		}
	| _ { proof_body ident n res lexbuf }
(* the rule for comments  *)
and comment_thm res = parse
	| "*)" { theorem res lexbuf }
	| _ {comment_thm res lexbuf }
and comment_name res = parse
	| "*)" { name res lexbuf }
	| _ {comment_name res lexbuf }
and comment_name' ident res = parse
	| "*)" { name' ident res lexbuf }
	| _ {comment_name' ident res lexbuf }
and comment_eater ident res = parse
	| "*)" { eater ident res lexbuf }
	| _ {comment_eater ident res lexbuf }
and comment_proof ident n res = parse
	| "*)" { proof_body ident n res lexbuf }
	| _ {comment_proof ident n res lexbuf }
