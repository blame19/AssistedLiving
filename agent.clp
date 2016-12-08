




;// AGENT





(defmodule AGENT (import MAIN ?ALL))





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
     (assert (K-agent (time 0) (step 0) (pos-r ?r) (pos-c ?c) (direction north)
                          (free 2) (waste no)))
)

(defrule ask_act

 ?f <-   (status (step ?i))

    =>  (printout t crlf crlf)

        (printout t "action to be executed at step:" ?i)

        (printout t crlf crlf)

        (modify ?f (work on)))





(defrule exec_act

    (status (step ?i))

    (exec (step ?i))

 => (focus MAIN))