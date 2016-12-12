;// PLANNER

(defmodule PLANNER (import MAIN ?ALL) (import AGENT ?ALL))


;//_______Functions


;//_______Rules

(defrule rcv_meal
	(msg-to-agent (request-time ?rqt) (step ?s) (sender ?P) (request meal) (t_pos-r ?tr) (t_pos-c ?tc))
	=>
	;1 answer the request
	(assert (exec (step ?s) (action Inform) (param1 ?P) (param2 meal) (param3 yes) (param4 nil)))
	;2 plan how to get the meal

)