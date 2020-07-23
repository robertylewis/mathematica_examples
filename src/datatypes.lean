/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/

import tactic.ring

open tactic
meta def mk_inhabitant_using (A : expr) (t : tactic unit) : tactic expr :=
prod.snd <$> solve_aux A t

meta definition eq_by_ring (e1 e2 : expr) : tactic expr :=
do gl ← mk_app `eq [e1, e2],
   --mk_inhabitant_using gl `[ring] <|> (fail "unable to simplify")
   prod.snd <$> solve_aux gl (`[ring] >> done) <|> (fail "unable to simplify")
