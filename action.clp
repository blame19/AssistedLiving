
;// ACTION

(defmodule ACTION (import MAIN ?ALL) (export ?ALL)  (import STRATEGY ?ALL))



;//_______Facts
(deftemplate translate_path (slot id))
(deftemplate current-step-counter (slot step))
(deftemplate node-counter (slot i))

(deftemplate copy-step (slot path-id) (slot node-id) (slot father-id) (slot node-r) (slot node-c) (slot direction))
(deftemplate number-of-steps (slot number))

;//_______Rules


(defrule read_todo_initialize
	(declare (salience 15))
	(exec-todo (id ?id))
	(todo (id ?id) (chosen_path ?path-id) (step ?s) (sender ?P) (request ?req))	
	=>
	(assert (translate_path (id ?path-id)))
	(assert (node-counter (i 0)))
)

(defrule current_step_initialize_0
	(declare (salience 15))
	(not (current-step-counter))
	=>
	(assert (current-step-counter (step 0)))
)

(defrule current_step_initialize
	(declare (salience 15))
	(K-agent (step ?step))
	?f <- (current-step-counter (step ?step2))
	(test (< ?step2 ?step))
	=>
	(modify ?f (step ?step))
	)

(defrule bump_step_initialize
	(declare (salience 14))
	(K-agent (step ?step))
	?f <- (current-step-counter (step ?step2))
	?g <- (action-notify (bump yes))
	
	=>
	(modify ?f (step ?step))
	(retract ?g)

	)

(defrule copy-path-steps
	(declare (salience 13))
	(translate_path (id ?path-id))	
	(path-step (path-id ?path-id) (node-id ?nid) (father-id ?fid) (node-r ?r) (node-c ?c) (direction ?dir))
	=>
	(assert (copy-step (path-id ?path-id) (node-id ?nid) (father-id ?fid) (node-r ?r) (node-c ?c) (direction ?dir)))
)

(defrule count-path-steps
	(declare (salience 13))
	(translate_path (id ?path-id))	
	(path-step (path-id ?path-id) (node-id ?nid) (father-id ?fid) (node-r ?r) (node-c ?c) (direction ?dir))
	(not (path-step (path-id ?path-id) (node-id ?nid2&:(> ?nid2 ?nid))))
	=>
	(assert (number-of-steps (number ?nid)))
)

; (defrule exec-preliminary-action
; 	(declare (salience 10))
; 	(exec-todo (id ?id))
; 	?g <- (current-step-counter (step ?step))
; 	(todo (id ?id) (chosen_path ?path-id) (step ?s) (sender ?P) (request ?req))
; 	=>
; 	(if (eq ?req load_meal)
; 		then (assert (proto-exec (step ?step) (action Inform) (param1 ?P) (param2 meal) (param3 yes) (param4 nil)))
;         	     (modify ?g (step (+ ?step 1)))
;     	)
; )


(defrule exec-path
	(declare (salience 10))
	(translate_path (id ?path-id))
        ;(K-agent (step ?step) (pos-r ?r) (pos-c ?c) (direction ?sdir))
        ?f <- (node-counter (i ?i))
        ?g <- (current-step-counter (step ?step))
        (copy-step (path-id ?path-id) (node-id ?i) (father-id ?fid) (node-r ?r1) (node-c ?c1) (direction ?dir1))
        (copy-step (path-id ?path-id) (node-id ?y) (father-id ?i) (node-r ?r2) (node-c ?c2) (direction ?dir2))
        (test (neq ?i ?y))
        (number-of-steps (number ?max))
        (test (< ?i ?max))
        (exec-todo (id ?id))
        =>
        (if (neq ?dir1 ?dir2)
        	then ;TURN ROBOT
        		(switch (turn ?dir1 ?dir2)
        			(case left then 
        				(assert (proto-exec (todo-id ?id) (step ?step) (action Turnleft)))
        				(modify ?g (step (+ ?step 1))))
        			(case right then 
        				(assert (proto-exec (todo-id ?id) (step ?step) (action Turnright)))
        				(modify ?g (step (+ ?step 1))))
        		)
        	else ;GO FORWARD
        		(assert (proto-exec (todo-id ?id) (step ?step) (action Forward)))
        		(modify ?g (step (+ ?step 1)))

        )
        (modify ?f (i (+ ?i 1)))
)



;All'ultimo passo del percorso l'agente ha raggiunto la posizione di goal (goal_pos)
;può quindi eseguire l'azione che voleva fare, indicata dalla ?req nel todo
(defrule exec-path-last-step
	(declare (salience 9))
	?h <- (translate_path (id ?path-id))
        ;(K-agent (step ?step) (pos-r ?r) (pos-c ?c) (direction ?sdir))
        ?f <- (node-counter (i ?i))
        ?g <- (current-step-counter (step ?step))        
        ?l <- (number-of-steps (number ?max))
        (test (= ?i ?max))

        ?k <- (exec-todo (id ?id))
	(todo (id ?id) (chosen_path ?path-id) (step ?s) (sender ?P) (request ?req) (goal_pos-r ?gr) (goal_pos-c ?gc))
	(prescription (patient ?P2) (meal ?type) (pills ?pills))
	(test (or (and (neq ?P nil) (eq ?P ?P2)) (eq ?P nil) ))
        (copy-step (path-id ?path-id) (node-id ?i) (father-id ?fid) (node-r ?r1) (node-c ?c1) (direction ?dir1))
        ;(not (copy-step (path-id ?path-id) (node-id ?y&:(> ?y ?i)) (father-id ?i)))        
        =>
        (switch ?req 
        	(case load_meal then (assert (proto-exec (todo-id ?id) (step ?step) (action LoadMeal) (param1 ?gr) (param2 ?gc) (param3 ?type) (last-action yes) ))
        				(modify ?g (step (+ ?step 1))))
        	(case meal then (assert (proto-exec (todo-id ?id) (step ?step) (action DeliveryMeal) (param1 ?gr) (param2 ?gc) (param3 ?type) (last-action yes)))
        				(modify ?g (step (+ ?step 1))))
        	(case load_dessert then (assert (proto-exec (todo-id ?id) (step ?step) (action LoadDessert) (param1 ?gr) (param2 ?gc) (last-action yes)))
        				(modify ?g (step (+ ?step 1))))
        	(case dessert then (assert (proto-exec (todo-id ?id) (step ?step) (action DeliveryDessert) (param1 ?gr) (param2 ?gc) (last-action yes)))
        				(modify ?g (step (+ ?step 1))))
        	(case load_pills then (assert (proto-exec (todo-id ?id) (step ?step) (action LoadPill) (param1 ?gr) (param2 ?gc) (param3 ?P) (last-action yes)))
        				(modify ?g (step (+ ?step 1))))
        	(case meal_before then  (assert (proto-exec (todo-id ?id) (step ?step) (action DeliveryPill) (param1 ?gr) (param2 ?gc) (param3 ?P)))
        				(assert (proto-exec (todo-id ?id) (step (+ ?step 1)) (action DeliveryMeal) (param1 ?gr) (param2 ?gc) (param3 ?type) (last-action yes)))
        				(modify ?g (step (+ ?step 2))))
        	(case meal_after then  (assert (proto-exec (todo-id ?id) (step ?step) (action DeliveryMeal) (param1 ?gr) (param2 ?gc) (param3 ?type)))
        		(assert (proto-exec (todo-id ?id) (step (+ ?step 1)) (action DeliveryPill) (param1 ?gr) (param2 ?gc) (param3 ?P) (last-action yes)))
        		(modify ?g (step (+ ?step 2))))
        	(case clean_table then (assert (proto-exec (todo-id ?id) (step ?step) (action CleanTable) (param1 ?gr) (param2 ?gc) (last-action yes)))
        				(modify ?g (step (+ ?step 1))))
        	(case empty_trash then (assert (proto-exec (todo-id ?id) (step ?step) (action ReleaseTrash) (param1 ?gr) (param2 ?gc) (last-action yes)))
        				(modify ?g (step (+ ?step 1))))
        )
        (retract ?h)
        (retract ?k)
        (retract ?l)
        ;(focus AGENT)
)


(defrule purge_copy_steps
	 ?f <- (copy-step )
	 =>
	 (retract ?f)
	)

(defrule purge_node_counter
	 ?f <- (node-counter)
	 =>
	 (retract ?f)
	)


(defrule go_agent
	(not (copy-step))
	=>
	(focus AGENT)
	)

