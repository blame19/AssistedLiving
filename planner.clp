;// PLANNER

(defmodule PLANNER (import MAIN ?ALL) (import AGENT ?ALL))



;//_______Facts

;//_______Functions

;//_______Rules

(defrule rcv_meal
	(msg-to-agent (request-time ?rqt) (step ?s) (sender ?P) (request meal) (t_pos-r ?tr) (t_pos-c ?tc))
	?f <- (K-received-msg (step ?s) (sender ?P) (request meal) (t_pos-r ?tr) (t_pos-c ?tc))
	(K-agent (free ?free) (waste ?waste))
	=>
	;1 answer the request
	(assert (exec (step ?s) (action Inform) (param1 ?P) (param2 meal) (param3 yes) (param4 nil)))	
	(modify ?f (taken yes))
	;2 plan how to get the meal
	(if (and (> ?free 0) (neq ?waste yes)) 
		then (printout t "must get meal")
			(focus AGENT)
		else (printout t "must make room")
		)
)

(defrule rcv_dessert
	(msg-to-agent (request-time ?rqt) (step ?s) (sender ?P) (request dessert) (t_pos-r ?tr) (t_pos-c ?tc))
	?f <- (K-received-msg (step ?s) (sender ?P) (request dessert) (t_pos-r ?tr) (t_pos-c ?tc))
	=>
	;1 answer the request
	(assert (exec (step ?s) (action Inform) (param1 ?P) (param2 dessert) (param3 yes) (param4 nil)))	
	(modify ?f (taken yes))
	;2 plan how to get the dessert
)