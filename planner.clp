;// PLANNER

(defmodule PLANNER (import MAIN ?ALL) (export ?ALL) (import AGENT ?ALL))



;//_______Facts

(deftemplate get-meal (slot step) (slot sender) (slot t_pos-r) (slot t_pos-c) (slot type))
(deftemplate get-pills (slot step) (slot sender) (slot t_pos-r) (slot t_pos-c) (slot when))




(deftemplate obj-goal-pos (slot id) (slot pos-r) (slot pos-c))
(deftemplate candidate-goal-pos (slot id) (slot pos-r) (slot pos-c))
(deftemplate goal-pos (slot id) (slot pos-r) (slot pos-c))

;Va aggiunta una qualche sorta di lista delle azioni da mandare in exec (da gestire tramite gli "step" numerici)

;//_______Functions

;//_______Rules

;Si attiva quando viene ricevuto un messaggio dall'agente di tipo request=meal, e l'agente passa il focus
(defrule rcv_msg_meal
	(msg-to-agent (request-time ?rqt) (step ?s) (sender ?P) (request meal) (t_pos-r ?tr) (t_pos-c ?tc))
	?f <- (K-received-msg (step ?s) (sender ?P) (request meal) (t_pos-r ?tr) (t_pos-c ?tc))
	(K-agent (free ?free) (waste ?waste))	
	(prescription (patient ?P) (meal ?meal) (pills ?pills) (dessert ?dessert))
	=>
	;1 answer the request
	(assert (exec (step ?s) (action Inform) (param1 ?P) (param2 meal) (param3 yes) (param4 nil)))	
	(modify ?f (taken yes))
	;2 plan how to get the meal
	(if (neq ?pills no) then 
		(if (and (> ?free 1) (neq ?waste yes)) 
			then (printout t "must get meal and pills")
				(assert (get-meal (step ?s) (sender ?P) (t_pos-r ?tr) (t_pos-c ?tc) (type ?meal)))
				(assert (get-pills (step ?s) (sender ?P) (t_pos-r ?tr) (t_pos-c ?tc) (when ?pills)))						
			else (printout t "must make room")
				;TODO : gestire lo spazio
		)
		
	else (if (and (> ?free 0) (neq ?waste yes)) 
		then (printout t "must get meal")
			(assert (get-meal (step ?s) (sender ?P) (t_pos-r ?tr) (t_pos-c ?tc) (type ?meal)))			
		else (printout t "must make room")
		;TODO : gestire lo spazio
		)
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


;Si attiva quando esiste un fatto di tipo get-meal e quindi bisogna pianificare
;Il percorso fino al meal dispenser e il carico
;bisogna ricordare che questa regola si attiva quando è già stata mandata un'exec di tipo Inform per accettare la richiesta di pasto
;di conseguenza se vengono lanciate ulteriori exec devono avere step maggiore di quello dell'inform (vedi regola rcv_msg_meal)
(defrule get_to_meal_disp 
	(get-meal (step ?s) (sender ?P) (t_pos-r ?tr) (t_pos-c ?tc) (type ?type))
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
		then
			(assert (exec (step (+ ?s 1)) (action LoadMeal) (param1 ?rdisp) (param2 ?cdisp) (param3 ?type)))
			;Qui si possono fare due cose :
			; 1 Lasciare il comando all'agente, fargli prendere il carico, e vedere se nel frattempo arrivano altre richieste
			;    ricordando che la LoadMeal impiega 15 unità di tempo, potrebbe essere conveniente
			;	(focus AGENT)
			; 2 Passare al planning del percorso per il tavolo ?tr ?tc
			 (assert (obj-goal-pos (id ?s) (pos-r ?tr) (pos-c ?tc)))
	else 
		;TODO: raggiungi il meal dispenser
		(printout t "dove?" clrf)
	)	
)

;regola per capire quali celle libere ci sono attorno a un tavolo o a un dispenser
;fa il calcolo basandosi sulla conoscenza dell'agente
;genera dei "candidati" a posizione di goal, che devono essere poi usati per calcolare un percorso ottimale
(defrule goal_near_object 
	(declare (salience 10))
	?f <- (obj-goal-pos (id ?s) (pos-r ?tr) (pos-c ?tc))
	(K-cell (pos-r ?r) (pos-c ?c) (contains Empty))
	(test (or (and (= ?tr ?r) (= ?tc (+ ?c 1)))
			  (and (= ?tr ?r) (= ?tc (- ?c 1)))
			  (and (= ?tr (+ ?r 1)) (= ?tc ?c))
			  (and (= ?tr (- ?r 1)) (= ?tc ?c))
		)
	)
	=> 
	(assert (candidate-goal-pos (id ?s) (pos-r ?r) (pos-c ?c)))	
)

(defrule ask_to_module_path
	(declare (salience 9))
	(candidate-goal-pos (pos-r ?r) (pos-c ?c))
	=> 
	(focus PATH)
)

