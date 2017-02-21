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

(deftemplate K-table
	(slot t_pos-r)
	(slot t_pos-c)
	(slot clean (allowed-values yes no))
	(slot meal_delivered_at_time)
)


(deftemplate proto-exec (slot todo-id) (slot step) (slot action) (slot param1) (slot param2) (slot param3) (slot param4) (slot last-action (default no)))

(deftemplate K-exec (slot step) (slot action) (slot param1) (slot param2) (slot param3) (slot param4))
(deftemplate executed-todo (slot todo-id))

(deftemplate max_duration (slot time))
(deftemplate bump-avoid (slot todo-id) (slot step) (slot pos-r) (slot pos-c) (slot intent))

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

(defrule  beginagent_1
    (declare (salience 11))
    (status (step 0))
    (not (exec (step 0)))
    (prior-cell (pos-r ?r) (pos-c ?c) (contains ?x)) 
	=>
	(assert (K-cell (pos-r ?r) (pos-c ?c) (contains ?x)))
	(if (eq ?x Table) 
		then 
		(assert (K-table (t_pos-r ?r) (t_pos-c ?c) (clean yes)) )
	)
)

(defrule  beginagent_2
      (declare (salience 10))
      (status (step 0))
      (not (exec (step 0)))
      (maxduration ?d)
      (K-cell (pos-r ?r) (pos-c ?c) (contains Parking))  
      =>
      (assert (K-agent (time 0) (step 0) (pos-r ?r) (pos-c ?c) (content Empty) (direction north) (free 2) (waste no)))
      (assert (max_duration (time ?d)))	
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
	;(focus STRATEGY)
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
		(assert (exec (step ?s) (action Inform) (param1 ?P) (param2 dessert) (param3 reject) (param4 nil)))
		else 
		;(focus STRATEGY)
	)		

)

	
; Ho stabilito che al primo step l'azione sia una wait, per avere le percezioni	
(defrule ask_act_0	
 	?f <-   (status (step 0))
 	(not (exec))
    	=>  
    	(printout t crlf crlf)
    	(printout t " AGENT" crlf)
        (printout t " first action: wait to get perceptions")
        (printout t crlf crlf)
        (modify ?f (work on))		
		(assert (exec (step 0) (action Wait)))			
)


; Notifica nella finestra di dialogo che c'è stato un bump, a fini di debugging
(defrule bump_alarm 
	(declare (salience 14))
	(perc-bump (time ?time) (step ?s) (pos-r ?r) (pos-c ?c) (direction ?d) )
	=>
	(printout t crlf crlf)
	(printout t " AGENT" crlf)
	(printout t " errore, ho fatto un bump in " ?r " " ?c " andando verso " ?d)         
	(printout t crlf crlf)
	(halt)
)


; Inizio procedura per evitare i bump
(defrule bump_avoid_initiate_repath
	(declare (salience 14))
	(perc-vision (time ?time) (step ?step) (pos-r ?r) (pos-c ?c) (direction ?d) (perc1 ?perc1) (perc2 ?perc2) (perc3 ?perc3) (perc4 ?perc4) (perc6 ?perc6) (perc7 ?perc7) (perc8 ?perc8) (perc9 ?perc9))
	(K-agent (step ?step))
	(proto-exec (todo-id ?id) (step ?step) (action Forward))
	?f <- (K-cell (pos-r ?kr) (pos-c ?kc) (contains ?cont))
	(test  (eq ?perc2 PersonStanding) )
	(test (or (and (eq ?d south) (= ?kr (- ?r 1)) (= ?kc ?c))                
		  (and (eq ?d north) (= ?kr (+ ?r 1)) (= ?kc ?c))                
		  (and (eq ?d east) (= ?kr ?r) (= ?kc (+ ?c 1)))                
		  (and (eq ?d west) (= ?kr ?r) (= ?kc (- ?c 1)))
		)                
	)
	=>
	(printout t crlf crlf)
	(printout t " AGENT" crlf)
	(printout t " bump detected")         
	(printout t crlf crlf)
	(assert (bump-avoid (todo-id ?id) (step ?step) (pos-r ?kr) (pos-c ?kc) ))
	(modify ?f (contains PersonStanding))
	(focus STRATEGY)
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
		(halt)
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
		(halt)
	)	
	(retract ?e)	
)

; Fa l'update del fatto K-agent in base alle percezioni di carico ricevute e ritira quello dello step precedente
; Si attiva dopo che è stata eseguita una LoadMeal
(defrule update_agent_load_pill
	(declare (salience 15))
	?e <- (perc-load (step ?step) (load yes))
	?f <- (K-agent (free ?fr) (content $?cont))	
	(K-exec (step ?step2) (action LoadPill) (param1 ?posr) (param2 ?posc) (param3 ?P))	
	(test (= ?step (+ ?step2 1)))	
	=>
	(if (> ?fr 0)
		then
		( if (eq ?fr 2) 
			then  	
				(modify ?f (step ?step) (free (- ?fr 1)) (content ?P) )
			else  (modify ?f (step ?step) (free (- ?fr 1)) (content (insert$ $?cont 1 ?P)) )
			)
		
		else        
		(printout t crlf crlf)
		(printout t "AGENT" crlf)
		(printout t "errore, Agente pieno")         
		(printout t crlf crlf)
		(halt)
	)	
	(retract ?e)	
)

(defrule update_agent_load_trash
	(declare (salience 15))
	;(perc-load (step ?step) (load yes))
    	?f <- (K-agent (step ?step) )
    	?g <- (K-table (t_pos-r ?tr) (t_pos-c ?tc) (clean no))
    	(K-exec (step ?step2) (action CleanTable) (param1 ?tr) (param2 ?tc) (param3 ?p3) (param4 ?p4))
    	(test (= ?step (+ ?step2 1)))	
    	=>
    	(modify ?f (step ?step) (waste yes) ) 
    	(modify ?g (clean yes))
    	(printout t crlf crlf)
	(printout t "AGENT" crlf)
	(printout t "Caricata spazzatura")         
	(printout t crlf crlf)    		
	
    	
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
	;?e <- (perc-load (step ?step) (load no))
	(K-exec (step ?step1) (action ?a) (param1 ?p1) (param2 ?p2) (param3 ?p3))
	?f <- (K-agent (step ?step1) (content $?c) (free ?fr))
	?g <- (K-received-msg (request ?req) (t_pos-r ?p1) (t_pos-c ?p2) (taken yes))		
	(test (< ?fr 2))
	;(test (= ?step (+ ?step1 1)))
	(test (member$ ?p3 $?c))
	(test (or (eq ?a DeliveryMeal) (eq ?a DeliveryPill) (eq ?a DeliveryDessert)))
	=> 
	(modify ?f (step (+ ?step1 1)) (content (delete-member$ $?c ?p3)) (free (+ ?fr 1)))
	(modify ?g (completed yes))
)


(defrule update_agent_unload_trash
	(declare (salience 15))	
	(K-exec (step ?step1) (action ReleaseTrash) (param1 ?p1) (param2 ?p2) (param3 ?p3))
	?f <- (K-agent (step ?step1) (waste yes))	
	;(test (= ?step (+ ?step1 1)))
	=> 
	(modify ?f (step (+ ?step1 1)) (waste no) )
)

;Trasforma una proto-exec in una exec
(defrule assert_exec	
	(declare (salience 12))
	(K-agent (step ?step))
	?f <- (proto-exec (todo-id ?id) (step ?step) (action ?a) (param1 ?p1) (param2 ?p2) (param3 ?p3) (param4 ?p4) (last-action ?value))
	;(not (proto-exec (step ?step2&:(< ?step2 ?step1)) ))
	=>
	(assert (exec (step ?step) (action ?a) (param1 ?p1) (param2 ?p2) (param3 ?p3) (param4 ?p4)))
	(if (eq ?value yes) 
		then (assert (executed-todo (todo-id ?id)))
	)
	(retract ?f)
)

(defrule update_table_dirty
	(declare (salience 3))
    	(K-agent (step ?i) (time ?time) (pos-r ?r) (pos-c ?c) (direction ?dir))
    	(exec (step ?i) (action DeliveryMeal) (param1 ?tr) (param2 ?tc) (param3 ?p3) (param4 ?p4))
    	(K-received-msg (step ?s) (sender ?P) (request meal) (t_pos-r ?tr) (t_pos-c ?tc)) 
    	?f <- (K-table (t_pos-r ?tr) (t_pos-c ?tc) (clean yes))
    	=>
    	(modify ?f (clean no) (meal_delivered_at_time ?time) )
)



;Controlla se ci sono delle exec programmate per questo step e le manda in esecuzione		
(defrule exec_act
	(declare (salience 2))
    	(K-agent (step ?i) (pos-r ?r) (pos-c ?c) (direction ?dir))
    	(exec (step ?i) (action ?a) (param1 ?p1) (param2 ?p2) (param3 ?p3) (param4 ?p4))    	
   	=> 
     	(assert (K-exec (step ?i) (action ?a) (param1 ?p1) (param2 ?p2) (param3 ?p3) (param4 ?p4)))

     	;Stampe a console
     	(if (or (eq ?a DeliveryMeal) (eq ?a DeliveryPill) (eq ?a DeliveryDessert)) 
     		then
		(printout t crlf crlf)
		(printout t " AGENT" crlf)
		(printout t " Delivery Action " ?a  " at step " ?i " while I am in " ?r " & " ?c )         
		(printout t crlf crlf)
	)

	(if (or (eq ?a LoadMeal) (eq ?a LoadDessert) (eq ?a LoadPill)) 
     		then
		(printout t crlf crlf)
		(printout t " AGENT" crlf)
		(printout t " Load Action " ?a  " at step " ?i " while I am in " ?r " & " ?c )         
		(printout t crlf crlf)
	)

	(if (eq ?a Forward) 
     		then
		(printout t crlf crlf)
		(printout t " AGENT" crlf)
		(printout t " going forward from " ?r " & " ?c " facing " ?dir)         
		(printout t crlf crlf)
	)

	(if (eq ?a EmptyRobot) 
     		then
		(printout t crlf crlf)
		(printout t " AGENT" crlf)
		(printout t " Emptied Robot Trash in " ?r " & " ?c " facing " ?dir)         
		(printout t crlf crlf)
	)

	(if (eq ?a CleanTable) 
     		then
		(printout t crlf crlf)
		(printout t " AGENT" crlf)
		(printout t " Cleaned table near " ?r " & " ?c " facing " ?dir)         
		(printout t crlf crlf)
	)
	(if (eq ?a Inform) 
     		then
		(printout t crlf crlf)
		(printout t " AGENT" crlf)
		(printout t " Informing " ?p1 " of request " ?p2 " result " ?p3)         
		(printout t crlf crlf)
		(halt)
	)
       	(focus MAIN)
)


;Se è stato ricevuto un messaggio, passa il controllo a Strategy per far si
;che lo traduca in un todo
;NOTA : la salience è più bassa di exec_act, probabilmente questa regola si attiva se non ci sono exec da fare.
;NON è detto che vada bene.
(defrule message_received_this_step
	(declare (salience 1))
	(K-received-msg (step ?step) )
	(K-agent (step ?step))
	=>
	(focus STRATEGY)
)

; ;Se non ci sono proto_exec in lista, l'agente ripassa a Strategy perché immagina 
; ;che si debba generare un altro piano
; (defrule proto_exec_finished
; 	(declare (salience 1))
;      	(not (proto-exec))
;      	=>  
;     	(focus STRATEGY)	
; )

; Comunica DONE quando il tempo sta per scadere
(defrule DONE_act
	(declare (salience 1))
 	?f <-   (status (step ?i) (time ?t))
 	(max_duration (time ?maxt))
 	(not (status (step 0)))
 	(test (> ?t (- ?maxt 20)))
    	=>  
    	;(printout t crlf crlf)
        ;(printout t "action to be executed at step:" ?i)
        ;(printout t crlf crlf)
        (modify ?f (work on))
        (assert (exec (step ?i) (action Done)))			
)

; Se non c'é nient'altro da fare, aspetta
; (defrule wait_act
; 	(declare (salience 0))
;  ?f <-   (status (step ?i))
;  (not (status (step 0)))
;  ;(not (exec (step (+ ?i 1))))
;     =>  
;     	;(printout t crlf crlf)
;         ;(printout t "action to be executed at step:" ?i)
;         ;(printout t crlf crlf)
;         (modify ?f (work on))
;         (assert (exec (step ?i) (action Wait)))			
; )
; 	

(defrule nothing_else_todo
 	(declare (salience 0))
      
      	=>  
     	(focus STRATEGY)	
)