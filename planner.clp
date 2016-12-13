;// PLANNER

(defmodule PLANNER (import MAIN ?ALL) (import AGENT ?ALL))



;//_______Facts

(deftemplate get_meal (slot id) (slot sender) (slot t_pos-r) (slot t_pos-c))

;Va aggiunta una qualche sorta di lista delle azioni da mandare in exec.

;//_______Functions

;//_______Rules

;Si attiva quando viene ricevuto un messaggio dall'agente di tipo request=meal, e l'agente passa il focus
(defrule rcv_msg_meal
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
			(assert (get_meal (id ?s) (sender ?P) (t_pos-r ?tr) (t_pos-c ?tc)))			
		else (printout t "must make room")
	)
)

;Si attiva quando viene ricevuto un messaggio dall'agente di tipo request=dessert, e l'agente passa il focus
(defrule rcv_msg_dessert
	(msg-to-agent (request-time ?rqt) (step ?s) (sender ?P) (request dessert) (t_pos-r ?tr) (t_pos-c ?tc))
	?f <- (K-received-msg (step ?s) (sender ?P) (request dessert) (t_pos-r ?tr) (t_pos-c ?tc))
	=>
	;1 answer the request
	(assert (exec (step ?s) (action Inform) (param1 ?P) (param2 dessert) (param3 yes) (param4 nil)))	
	(modify ?f (taken yes))
	;2 plan how to get the dessert
)


;Si attiva quando esiste un fatto di tipo get_meal e quindi bisogna pianificare
;Il percorso fino al meal dispenser e il carico
(defrule get_to_meal_disp 
	(get_meal (id ?i) (sender ?P) (t_pos-r ?tr) (t_pos-c ?tc))
	(K-agent (step ?sA) (time ?sT) (pos-r ?rA) (pos-c ?cA) (direction ?dir) (free ?fr) (waste ?w))
	(K-cell (pos-r ?rdisp) (pos-c ?cdisp) (contains MealDispenser))
	=>	
	;Controllo se l'agente è su uno dei quattro accessi al dispenser	
	(if 
		(or  
			(and (= ?rdisp ?rA) (= ?cdisp (+ ?cA 1)) )
			(and (= ?rdisp ?rA) (= ?cdisp (- ?cA 1)) )
			(and (= ?rdisp (+ ?rA 1)) (= ?cdisp ?cA ))
			(and (= ?rdisp (- ?rA 1)) (= ?cdisp ?cA))
		) 
		then (assert (exec (step ?sA) (action LoadMeal) (param1 ?rdisp) (param2 ?cdisp)))
			(focus AGENT)
	else 
	;TODO: raggiungi il meal dispenser
	(printout t "dove?")
	)
	

)