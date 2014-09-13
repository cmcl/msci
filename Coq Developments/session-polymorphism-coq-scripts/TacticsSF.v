Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Ltac Case name := Case_aux Case name.
Ltac SCase name := Case_aux SCase name.
Ltac SSCase name := Case_aux SSCase name.
Ltac SSSCase name := Case_aux SSSCase name.
Ltac SSSSCase name := Case_aux SSSSCase name.
Ltac SSSSSCase name := Case_aux SSSSSCase name.
Ltac SSSSSSCase name := Case_aux SSSSSSCase name.
Ltac SSSSSSSCase name := Case_aux SSSSSSSCase name.
Ltac SSSSSSSSCase name := Case_aux SSSSSSSSCase name.
Ltac SSSSSSSSSCase name := Case_aux SSSSSSSSSCase name.
