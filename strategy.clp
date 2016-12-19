;// STRATEGY

(defmodule STRATEGY (import MAIN ?ALL)   (export ?ALL) (import AGENT ?ALL))



;//_______Facts

;Fatto aggregato da passare ad Action 
; che contiene tutte le informazioni necessarie per soddisfare la richiesta, generando un piano
;ricordarsi che se necessario gli slot possono essere lasciati a null
(deftemplate to_action
        (slot step)
        (slot sender)
        (slot request)
        ;se la richista prevede la posizione (normale, di cella vuota)
        (slot pos-r) (slot pos-c)
        ;se la richiesta prevede la posizione di un tavolo
        (slot t_pos-r) (slot t_pos-c)
        ;parametri opzionali
        (slot type_of_meal)
        (slot pills)
)

;//_______Rules


(defrule request_from_message
        ?g <- (msg-to-agent (request-time ?rqt) (step ?s) (sender ?P) (request ?request) (t_pos-r ?tr) (t_pos-c ?tc))
        ?f <- (K-received-msg (step ?s) (sender ?P) (request ?request) (t_pos-r ?tr) (t_pos-c ?tc))
        (K-agent (step ?step) (content ?con) (free ?free) (waste ?waste))   
        (prescription (patient ?P) (meal ?meal) (pills ?pills) (dessert ?dessert)) 
        =>
        ;TODO: Considerazioni sullo stato dell'agente e sul planning
        (assert (to_action (step ?step) (sender ?P) (request ?request) (t_pos-r ?tr) (t_pos-c ?tc) (type_of_meal ?meal) (pills ?pills)))
        


)