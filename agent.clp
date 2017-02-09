;// AGENT


(defmodule AGENT (import MAIN ?ALL) (export ?ALL))

;(defglobal ?*id-goal-pos* = 0 )


;//_______Templates
(deftemplate K-cell  (slot pos-r) (slot pos-c) (slot contains))

(deftemplate K-agent
	(slot step)
	(slot time) 
	(slot pos-r) 
	(slot pos-c) 
	(slot direction) 
	(multislot content)
	(slot free)
    (slot waste)
)

(deftemplate K-received-msg 
	(slot step)
	(slot sender)
	(slot request)
	(slot t_pos-r)
	(slot t_pos-c)	
	;slot per indicare se l'agente si è preso carico della richiesta
	(slot taken (allowed-values yes no))
	;slot per indicare se la richiesta è stata portata a termine dall'agente
	(slot completed (allowed-values yes no) (default no))
)

(deftemplate proto-exec (slot step) (slot action) (slot param1) (slot param2) (slot param3) (slot param4))

(deftemplate K-exec (slot step) (slot action) (slot param1) (slot param2) (slot param3) (slot param4))

;//_______Functions

; Funzione che restituisce "come muoversi" o "dove girarsi" per passare da una direzione
; all'altra. Dir1 è in genere la direzione dell'agente, dir2 quella desiderata. 
; restituisce left, right, same (se si è già allineati) e opposite (se le due direzioni sono opposte e non ha importanza dove girarsi)
(deffunction turn (?dir1 ?dir2) 
	(switch ?dir1
		(case north then 
			(switch ?dir2
				(case north then same)
				(case south then opposite)
				(case west then left)
				(case east then right)
			) 
		)
		(case south then
			(switch ?dir2
				(case north then opposite)
				(case south then same)
				(case west then right)
				(case east then left)
			) 
		)
		(case west then 
			(switch ?dir2
				(case north then right)
				(case south then left)
				(case west then same)
				(case east then opposite)
			) 
		)
		(case east then 
			(switch ?dir2
				(case north then left)
				(case south then right)
				(case west then opposite)
				(case east then same)
			) 
		)
	)
)

(deffunction manhattan (?r1 ?c1 ?r2 ?c2)
	(if (or (= (- ?r1 ?r2) 0) (= (- ?c1 ?c2) 0)) 
		then (+ (abs(- ?r1 ?r2)) (abs(- ?c1 ?c2)))

		else (+ (abs(- ?r1 ?r2)) (abs(- ?c1 ?c2)) 2) 
	)
)

;//_______Rules

(defrule  beginagent1
    (declare (salience 11))
    (status (step 0))
    (not (exec (step 0)))
    (prior-cell (pos-r ?r) (pos-c ?c) (contains ?x)) 
	=>
	(assert (K-cell (pos-r ?r) (pos-c ?c) (contains ?x)))
)

(defrule  beginagent2
      (declare (salience 10))
      (status (step 0))
      (not (exec (step 0)))
      (K-cell (pos-r ?r) (pos-c ?c) (contains Parking))  
	  =>
     (assert (K-agent (time 0) (step 0) (pos-r ?r) (pos-c ?c) (content Empty) (direction north) (free 2) (waste no)))
	 ;linee aggiunte rispetto al codice originale, per provare il cammino verso un goal
	 ;(assert (goal-pos (id 1) (pos-r 2) (pos-c 2)))
	 ;(assert (goal-achieve (status false)))
)

;Regola che si attiva all'arrivo di una richiesta di meal.
;Delega al ACTION la gestione della richiesta
;Salva inoltre una copia della richiesta in K-received-msg: la memoria dell'agente sui messaggi passati
(defrule on_meal_req_received
	(declare (salience 10))
	(msg-to-agent (step ?s) (sender ?P) (request meal) (t_pos-r ?tr) (t_pos-c ?tc))
	(prescription (patient ?P) (meal ?meal) (pills ?pills) (dessert ?dessert))
	(status (step ?i))
	(test (= ?s ?i))
	(not (K-received-msg (sender ?P) (request meal) (t_pos-r ?tr) (t_pos-c ?tc)))
	=>
	;aggiungo il messaggio alla lista dei ricevuti (e già esaminati)
	(assert (K-received-msg (step ?s) (sender ?P) (request meal) (t_pos-r ?tr) (t_pos-c ?tc)))
	(focus STRATEGY)
)

;Regola che si attiva all'arrivo di una richiesta di dessert.
;Delega al ACTION la gestione della richiesta SE:
; 1) è previsto che il paziente possa avere il dessert
; 2) TODO: all'agente risulta che il paziente abbia già consumato il meal 
;Salva inoltre una copia della richiesta in K-received-msg: la memoria dell'agente sui messaggi passati
(defrule on_dessert_req_received
	(declare (salience 10))
	(msg-to-agent (step ?s) (sender ?P) (request dessert) (t_pos-r ?tr) (t_pos-c ?tc))
	(prescription (patient ?P) (pills ?pills) (dessert ?dessert))
	;(consumed-meal (patient ?P)) condizione da aggiungere: se un paziente ha finito di mangiare il suo pranzo, riceve il dessert
	(status (step ?i))
	(test (= ?s ?i))	
	(not (K-received-msg (sender ?P) (request dessert) (t_pos-r ?tr) (t_pos-c ?tc)))
	=>	
	;aggiungo il messaggio alla lista dei ricevuti (e già esaminati)
	(assert (K-received-msg (step ?s) (sender ?P) (request dessert) (t_pos-r ?tr) (t_pos-c ?tc)))
	(if (neq ?dessert yes) then
		;Rifiuto della richiesta perché contraria alla prescrizione 
		(assert (exec (step ?s) (action Inform) (param1 ?P) (param2 dessert) (param3 rejected) (param4 nil)))
		else 
		(focus STRATEGY)
	)		

)



	
; Ho stabilito che al primo step l'azione sia una wait, per avere le percezioni	
(defrule ask_act_0	
 ?f <-   (status (step 0))
    =>  (printout t crlf crlf)
        (printout t "first action: wait to get perceptions")
        (printout t crlf crlf)
        (modify ?f (work on))		
		(assert (exec (step 0) (action Wait)))			
)

; Fa l'update del fatto K-agent in base alle percezioni visive ricevute e ritira quello dello step precedente
(defrule update_agent_vision 
	(declare (salience 14))
	(perc-vision (time ?time) (step ?s) (pos-r ?r) (pos-c ?c) (direction ?d))
	?f <- (K-agent (step ?sA) (free ?fr) (waste ?w))
	(test (< ?sA ?s))
	=>
	(modify ?f (time ?time) (step ?s) (pos-r ?r) (pos-c ?c) (direction ?d) (free ?fr) (waste ?w))
)	

; Fa l'update del fatto K-agent in base alle percezioni di carico ricevute e ritira quello dello step precedente
; Si attiva dopo che è stata eseguita una LoadMeal
(defrule update_agent_load_meal
	(declare (salience 15))
	?e <- (perc-load (step ?step) (load yes))
	?f <- (K-agent (free ?fr) (content $?cont))	
	(K-exec (step ?step2) (action LoadMeal) (param1 ?posr) (param2 ?posc) (param3 ?type))
	
	(test (= ?step (+ ?step2 1)))	
	=>
	(if (> ?fr 0)
		then
		( if (eq ?fr 2) 
			then  	
				(modify ?f (step ?step) (free (- ?fr 1)) (content ?type) )
			else  (modify ?f (step ?step) (free (- ?fr 1)) (content (insert$ $?cont 1 ?type)) )
			)
		
		else        
		(printout t crlf crlf)
		(printout t "AGENT")
		(printout t "errore, Agente pieno")         
		(printout t crlf crlf)
	)	
	(retract ?e)	
)

; Fa l'update del fatto K-agent in base alle percezioni di carico ricevute e ritira quello dello step precedente
; Si attiva dopo l'esecuzione di LoadDessert
(defrule update_agent_load_dessert
	(declare (salience 15))
	?e <- (perc-load (step ?step) (load yes))
	?f <- (K-agent (free ?fr) (content $?cont))	
	(K-exec (step ?step2) (action LoadDessert) (param1 ?posr) (param2 ?posc))
	
	(test (= ?step (+ ?step2 1)))	
	=>
	(if (> ?fr 0)
		then
		( if (eq ?fr 2) 
			then  	
				(modify ?f (step ?step) (free (- ?fr 1)) (content dessert) )
			else  (modify ?f (step ?step) (free (- ?fr 1)) (content (insert$ $?cont 1 dessert)) )
			)
		
		else        
		(printout t crlf crlf)
		(printout t "AGENT")
		(printout t "errore, Agente pieno")         
		(printout t crlf crlf)
	)	
	(retract ?e)	
)
; Scarica un elemento (quando è l'unico caricato e viene data una perc_load)
;va in conflitto con la successiva
;(defrule update_agent_unload_all
;	(declare (salience 15))
;	?e <- (perc-load (step ?step) (load no))
;	?f <- (K-agent (free 1))
;	=> 
;	(modify ?f (step ?step) (content Empty) (free 2))
;	(retract ?e)
;)

; Sceglie l'elemento da scaricare nella lista
;Servono le op sui multislot ...
(defrule update_agent_unload_one
	(declare (salience 15))		
	?e <- (perc-load (step ?step) (load no))
	(K-exec (step ?step1) (action ?a) (param1 ?p1) (param2 ?p2) (param3 ?p3))
	?f <- (K-agent (step ?step1) (content $?c) (free ?fr))
	?g <- (K-received-msg (request ?req) (t_pos-r ?p1) (t_pos-c ?p2) (taken yes))		
	(test (< ?fr 2))
	(test (= ?step (+ ?step1 1)))
	(test (member$ ?p3 $?c))
	=> 
	(if (or (eq ?a DeliveryMeal) (eq ?a DeliveryPills) (eq ?a DeliveryDessert))  
		then (modify ?f (step ?step) (content (delete-member$ $?c ?p3)) (free (+ ?fr 1)))
		(modify ?g (completed yes))
		else (printout t "do nothing")  )
	
)


;Trasforma una proto-exec in una exec
(defrule assert_exec	
	(declare (salience 12))
	(K-agent (step ?step))
	?f <- (proto-exec (step ?step) (action ?a) (param1 ?p1) (param2 ?p2) (param3 ?p3) (param4 ?p4))
	;(not (proto-exec (step ?step2&:(< ?step2 ?step1)) ))
	=>
	(assert (exec (step ?step) (action ?a) (param1 ?p1) (param2 ?p2) (param3 ?p3) (param4 ?p4)))
	(retract ?f)
)


(defrule proto_exec_finished
(declare (salience 1))
	(not (proto-exec))
     =>  
     (focus STRATEGY)	
)
	
(defrule ask_act
	(declare (salience 0))
 ?f <-   (status (step ?i))
 (not (status (step 0)))
 ;(not (exec (step (+ ?i 1))))
    =>  
    	;(printout t crlf crlf)
        ;(printout t "action to be executed at step:" ?i)
        ;(printout t crlf crlf)
        (modify ?f (work on))			
)
		
(defrule exec_act
	(declare (salience 2))
    (K-agent (step ?i))
    (exec (step ?i) (action ?a) (param1 ?p1) (param2 ?p2) (param3 ?p3) (param4 ?p4))
   
   => 
  (assert (K-exec (step ?i) (action ?a) (param1 ?p1) (param2 ?p2) (param3 ?p3) (param4 ?p4)))
  (focus MAIN)
)
