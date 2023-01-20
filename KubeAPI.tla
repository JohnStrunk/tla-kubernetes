------------------------------ MODULE KubeAPI ------------------------------
EXTENDS FiniteSets, Naturals, Sequences, TLC

CONSTANTS
    REQUESTS_CAN_FAIL,   \* API requests can fail randomly
    REQUESTS_CAN_TIMEOUT \* API requests/replies may timeout
    
ASSUME REQUESTS_CAN_FAIL \in BOOLEAN
ASSUME REQUESTS_CAN_TIMEOUT \in BOOLEAN

(* --fair algorithm KubeAPI
variables
    \* The contents of the API server
    apiState = {}, \* API Server starts empty
    \* The requests that are in-flight
    requests = [x \in {} |-> {}], \* Start w/ none
    listRequests = [x \in {} |-> {}] \* Start w/ none

define
    (***********************************************************************)
    (* API objects have a (n)ame and (k)ind.  They optionally have a spec  *)
    (* and status.  Additionally, they have a version vector (vv) that is  *)
    (* the set of clients that have read the current version of the API    *)
    (* object.  This is used to determine whether the precondition is met  *)
    (* for an update operation.                                            *)
    (***********************************************************************)
    IsValidAPIObject(o) ==
        \* Must have name, key
        /\ {"n", "k"} \subseteq DOMAIN o
        \* May also have spec, status
        /\ DOMAIN o \subseteq {"n", "k", "vv", "spec", "status"}
        \* Name and kind fields must have proper type
        /\ o.n \in STRING /\ o.k \in STRING
    
    (***********************************************************************)
    (* True if one object is a version of another (i.e., name and kind     *)
    (* match)                                                              *)
    (***********************************************************************)
    IsVersionOf(o1, o2) == o1.n = o2.n /\ o1.k = o2.k

    (***********************************************************************)
    (* When an object is written, its version vector must be cleared.      *)
    (***********************************************************************)
    Write(o) == "vv" :> {} @@ o
    (***********************************************************************)
    (* When a client reads an object, add it to the version vector         *)
    (***********************************************************************)
    Read(o, c) == [o EXCEPT !.vv = @ \cup {c}]
    (***********************************************************************)
    (* True if this version of the object has been read by the specific    *)
    (* client.                                                             *)
    (***********************************************************************)
    HasRead(o, c) == c \in o.vv

    (***********************************************************************)
    (* ObjectExists(obj) is TRUE iff there exists a version of the object  *)
    (* currently in the API server                                         *)
    (***********************************************************************)
    ObjectExists(obj) == \E o \in apiState: IsVersionOf(o, obj)

    (***********************************************************************)
    (* Types of API operations                                             *)
    (***********************************************************************)
    Verbs == {"Create", "Get", "Update", "Delete", "Force"}

    (***********************************************************************)
    (* Requests start in "Pending" then move to one of the other states    *)
    (* once they have been serviced.                                       *)
    (***********************************************************************)
    Responses == {"Pending", "Ok", "Error"}

    (***********************************************************************)
    (* Requests have an (op)eration type, API (obj)ect, and request status *)
    (***********************************************************************)
    IsValidRequest(r) ==
        /\ {"op", "obj", "status"} = DOMAIN r
        /\ r.op \in Verbs
        /\ IsValidAPIObject(r.obj)
        /\ r.status \in Responses
        
    IsValidListRequest(r) ==
        /\ {"kind", "objs", "status"} = DOMAIN r
        /\ \A o \in r.objs: /\ IsValidAPIObject(o)
                            /\ o.k = r.kind
        /\ r.status \in Responses

    (***********************************************************************)
    (* The set of clients w/ pending requests                              *)
    (***********************************************************************)
    PendingClients == {c \in DOMAIN requests: requests[c].status = "Pending"}    
    PendingListClients == {c \in DOMAIN listRequests: listRequests[c].status = "Pending"}
    
    IsUnboundPVC(pvc) == /\ pvc.k = "PVC"
                         /\ \/ "spec" \notin DOMAIN pvc
                            \/ "pvname" \notin DOMAIN pvc.spec
end define;


(***************************************************************************)
(* Execute an API call by making a request then synchronously waiting for  *)
(* the response                                                            *)
(***************************************************************************)
procedure API(op, obj) begin
DoRequest:
    either \* Send the request
        \* We use this syntax bacause we may be expanding the DOMAIN of requests
        requests := self :> [op |-> op,
                             obj |-> obj,
                             status |-> "Pending"]
                    @@ requests;
    or \* Request failed or timed out sending to API server
        when REQUESTS_CAN_FAIL \/ REQUESTS_CAN_TIMEOUT;
        requests := self :> [op |-> op,
                             obj |-> obj,
                             status |-> "Error"]
                    @@ requests;
    end either;
DoReply:
    \* Block until the operation is complete (no longer Pending)
    await requests[self].status # "Pending";
    either
        skip;
    or
        \* Request timed out during reply
        when REQUESTS_CAN_TIMEOUT;
        requests[self].status := "Error";
    end either;
    return;
end procedure;

procedure ListAPI(kind) begin
DoListRequest:
    either \* send the request
        listRequests := self :> [kind |-> kind,
                                 objs |-> {},
                                 status |-> "Pending"]
                        @@ listRequests;
    or \* Request failed or timed out sending to API server
        when REQUESTS_CAN_FAIL \/ REQUESTS_CAN_TIMEOUT;
        listRequests := self :> [kind |-> kind,
                                 objs |-> {},
                                 status |-> "Error"]
                        @@ listRequests;
    end either;
DoListReply:
    await listRequests[self].status # "Pending";
    either
        skip;
    or
        \* Request timed out during reply
        when REQUESTS_CAN_TIMEOUT;
        listRequests[self].objs := {} || listRequests[self].status := "Error";
    end either;
    return;
end procedure;

(***************************************************************************)
(* Process Client implements the logic of the operator, trying to          *)
(* reconcile the objects in order to obtain the desired state              *)
(***************************************************************************)
process Client \in {"Client"}
variables
    shouldReconcile \in BOOLEAN;

begin CStart:
    \* The schedule will kick off a reconcile cycle periodically
    either
        shouldReconcile := TRUE;
    or
        skip;
    end either;

    \* Reconcile loop
    if shouldReconcile then \* Reconcile the objects
        \* try to create object
        call API("Force", [k |-> "Secret", n |-> "foo"]);
    C1:
        if requests[self].status # "Ok" then
            goto CStart;
        end if;
    C10:
        call API("Force", [k |-> "PVC", n |-> "mypvc"]);
    C11:
        if requests[self].status # "Ok" then
            goto CStart;
        end if;
    c12:
        call API("Get", [k |-> "PVC", n |-> "mypvc"]);
    C13:
        if requests[self].status # "Ok" \/ IsUnboundPVC(requests[self].obj) then
            goto CStart;
        end if;
    C2:
        \* Fully reconciled
        shouldReconcile := FALSE;
        assert ObjectExists([k |-> "Secret", n |-> "foo"]);
    else \* Clean up the objects
        call ListAPI("Secret");
    C3:
        if listRequests[self].status # "Ok" then
            goto CStart;
        end if;
    C8:
        if listRequests[self].objs = {} then
            goto C4;
        end if;
    C6:
        with s \in listRequests[self].objs do
            call API("Delete", [k |-> s.k, n |-> s.n]);
        end with;
    C7:
        if requests[self].status # "Ok" \/ Cardinality(listRequests[self].objs) > 1 then
            goto CStart;
        end if;
    C4:
        assert ~ObjectExists([k |-> "Secret", n |-> "foo"]);
    end if;
C5:
    goto CStart;
end process;

(***************************************************************************)
(* PVCController is responsible for watching PVCs and binding them to a PV *)
(***************************************************************************)
process PVCController \in {"PVCController"}
begin PVCStart:
    \* Get a list of all PVCs
    call ListAPI("PVC");
PVCListedPVCs:
    \* If we didn't find any, we try again
    if \/ listRequests[self].status # "Ok"
       \/ {o \in listRequests[self].objs: IsUnboundPVC(o)} = {} then
        goto PVCStart;
    end if;
PVCHavePVCs:
    \* Pick an arbitrary *unbound* PVC to work on
    with unb \in {o \in listRequests[self].objs: IsUnboundPVC(o)} do
        with bound = IF "spec" \notin DOMAIN unb THEN
                        "spec" :> ("pvname" :> unb.n) @@ unb
                     ELSE
                        [unb EXCEPT !.spec = "pvname" :> unb.n @@ @] do
            call API("Update", bound);
        end with;
    end with;
\*PVCLocalPVC:
\*    pvc := case "spec" \notin DOMAIN pvc -> "spec" :> ("pvname" :> pvc.n) @@ pvc
\*            /\ "spec" \in DOMAIN pvc
\*                /\ "pvn
\*    if "spec" \notin DOMAIN pvc then
\*        pvc.spec := "pvname" :> pvc.n
\*    end if;
\*PVCLocalPVCHasSpec:
\*    if "pvname" \notin DOMAIN pvc.spec then
\*        pvc.spec.pvname := pvc.n
\*    end if;
\*PVCUpdatePVC:
\*    call API("Update", pvc);
PVCDone:
    goto PVCStart;
end process;

(***************************************************************************)
(* Process APIServer represents the API server.  It services pending       *)
(* requests and updates the current set of objects held in the API server  *)
(* (apiState).  Requests made to the server may fail or timeout based on   *)
(* the constants REQUESTS_CAN_FAIL and REQUESTS_CAN_TIMEOUT.               *)
(***************************************************************************)
process APIServer \in {"Server"} begin APIStart:
    while TRUE do
        \* Outstanding requests can be serviced in any order
        either
            with c \in PendingClients do \* single-obj API requests
                (***********************************************************)
                (* Create                                                  *)
                (***********************************************************)
                if requests[c].op = "Create" then
                    if \E o \in apiState: IsVersionOf(o, requests[c].obj) then
                        \* Creating an object that already exists is an error
                        requests[c].status := "Error";
                    else
                        \* Successful create
                        apiState := apiState \cup {Write(requests[c].obj)};
                        requests[c].status := "Ok";
                    end if;
                (***********************************************************)
                (* Force                                                   *)
                (*                                                         *)
                (* This isn't a real verb.  It is a combination of Create  *)
                (* & Update wherein it replaces any existing object,       *)
                (* creating it if it isn't already present.                *)
                (***********************************************************)
                elsif requests[c].op = "Force" then
                    if \E o \in apiState: IsVersionOf(o, requests[c].obj) then
                        \* Replace the existing
                        apiState := { 
                            IF IsVersionOf(o, requests[c].obj) THEN
                                Write(requests[c].obj)
                            ELSE
                                o
                            : o \in apiState};
                    else
                        \* Create it
                        apiState := apiState \cup {Write(requests[c].obj)}; 
                    end if;
                    requests[c].status := "Ok";
                (***********************************************************)
                (* Get                                                     *)
                (***********************************************************)
                elsif requests[c].op = "Get" then
                    if \E o \in apiState: IsVersionOf(o, requests[c].obj) then
                        requests[c].obj := CHOOSE o \in apiState:
                                            IsVersionOf(o, requests[c].obj) ||
                            requests[c].status := "Ok";
                        apiState := { 
                            IF IsVersionOf(o, requests[c].obj) THEN
                                Read(o, c)
                            ELSE
                                o
                            : o \in apiState};
                    else
                        \* Object not found
                        requests[c].status := "Error";
                    end if;
                (***********************************************************)
                (* Delete                                                  *)
                (***********************************************************)
                elsif requests[c].op = "Delete" then
                    apiState := {o \in apiState: ~IsVersionOf(o, requests[c].obj)};
                    requests[c].status := "Ok";
                (***********************************************************)
                (* Update                                                  *)
                (***********************************************************)
                elsif requests[c].op = "Update" then
                    if \E o \in apiState: (IsVersionOf(o, requests[c].obj) /\ HasRead(o, c)) then
                        \* replace existing object
                        apiState :=
                            {o \in apiState: ~IsVersionOf(o, requests[c].obj)}
                            \cup
                            {Write(requests[c].obj)};
                            requests[c].status := "Ok";
                    else
                        \* Object not found or client hasn't read it
                        requests[c].status := "Error";
                    end if;
                else
                    \* Illegal command, but an Invariant would be violated
                    \* before we get here.
                    assert FALSE;
                end if;
            end with;
        or
            (*******************************************************************)
            (* List                                                            *)
            (*******************************************************************)
            with c \in PendingListClients do
                \* We don't consider an empty list result to be an error
                listRequests[c].objs := {o \in apiState: o.k = listRequests[c].kind} ||
                listRequests[c].status := "Ok"; 
                apiState := {
                    IF o.k = listRequests[c].kind THEN
                        Read(o, c)
                    ELSE
                        o
                    : o \in apiState};
            end with;
        end either;
    end while;
end process;
end algorithm; *)

-----------------------------------------------------------------------------

\* BEGIN TRANSLATION (chksum(pcal) = "92134e4e" /\ chksum(tla) = "bd196c85")
CONSTANT defaultInitValue
VARIABLES apiState, requests, listRequests, pc, stack

(* define statement *)
IsValidAPIObject(o) ==

    /\ {"n", "k"} \subseteq DOMAIN o

    /\ DOMAIN o \subseteq {"n", "k", "vv", "spec", "status"}

    /\ o.n \in STRING /\ o.k \in STRING





IsVersionOf(o1, o2) == o1.n = o2.n /\ o1.k = o2.k




Write(o) == "vv" :> {} @@ o



Read(o, c) == [o EXCEPT !.vv = @ \cup {c}]




HasRead(o, c) == c \in o.vv





ObjectExists(obj) == \E o \in apiState: IsVersionOf(o, obj)




Verbs == {"Create", "Get", "Update", "Delete", "Force"}





Responses == {"Pending", "Ok", "Error"}




IsValidRequest(r) ==
    /\ {"op", "obj", "status"} = DOMAIN r
    /\ r.op \in Verbs
    /\ IsValidAPIObject(r.obj)
    /\ r.status \in Responses

IsValidListRequest(r) ==
    /\ {"kind", "objs", "status"} = DOMAIN r
    /\ \A o \in r.objs: /\ IsValidAPIObject(o)
                        /\ o.k = r.kind
    /\ r.status \in Responses




PendingClients == {c \in DOMAIN requests: requests[c].status = "Pending"}
PendingListClients == {c \in DOMAIN listRequests: listRequests[c].status = "Pending"}

IsUnboundPVC(pvc) == /\ pvc.k = "PVC"
                     /\ \/ "spec" \notin DOMAIN pvc
                        \/ "pvname" \notin DOMAIN pvc.spec

VARIABLES op, obj, kind, shouldReconcile

vars == << apiState, requests, listRequests, pc, stack, op, obj, kind, 
           shouldReconcile >>

ProcSet == ({"Client"}) \cup ({"PVCController"}) \cup ({"Server"})

Init == (* Global variables *)
        /\ apiState = {}
        /\ requests = [x \in {} |-> {}]
        /\ listRequests = [x \in {} |-> {}]
        (* Procedure API *)
        /\ op = [ self \in ProcSet |-> defaultInitValue]
        /\ obj = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure ListAPI *)
        /\ kind = [ self \in ProcSet |-> defaultInitValue]
        (* Process Client *)
        /\ shouldReconcile \in [{"Client"} -> BOOLEAN]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in {"Client"} -> "CStart"
                                        [] self \in {"PVCController"} -> "PVCStart"
                                        [] self \in {"Server"} -> "APIStart"]

DoRequest(self) == /\ pc[self] = "DoRequest"
                   /\ \/ /\ requests' = (self :> [op |-> op[self],
                                                  obj |-> obj[self],
                                                  status |-> "Pending"]
                                         @@ requests)
                      \/ /\ REQUESTS_CAN_FAIL \/ REQUESTS_CAN_TIMEOUT
                         /\ requests' = (self :> [op |-> op[self],
                                                  obj |-> obj[self],
                                                  status |-> "Error"]
                                         @@ requests)
                   /\ pc' = [pc EXCEPT ![self] = "DoReply"]
                   /\ UNCHANGED << apiState, listRequests, stack, op, obj, 
                                   kind, shouldReconcile >>

DoReply(self) == /\ pc[self] = "DoReply"
                 /\ requests[self].status # "Pending"
                 /\ \/ /\ TRUE
                       /\ UNCHANGED requests
                    \/ /\ REQUESTS_CAN_TIMEOUT
                       /\ requests' = [requests EXCEPT ![self].status = "Error"]
                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                 /\ op' = [op EXCEPT ![self] = Head(stack[self]).op]
                 /\ obj' = [obj EXCEPT ![self] = Head(stack[self]).obj]
                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                 /\ UNCHANGED << apiState, listRequests, kind, shouldReconcile >>

API(self) == DoRequest(self) \/ DoReply(self)

DoListRequest(self) == /\ pc[self] = "DoListRequest"
                       /\ \/ /\ listRequests' = (self :> [kind |-> kind[self],
                                                          objs |-> {},
                                                          status |-> "Pending"]
                                                 @@ listRequests)
                          \/ /\ REQUESTS_CAN_FAIL \/ REQUESTS_CAN_TIMEOUT
                             /\ listRequests' = (self :> [kind |-> kind[self],
                                                          objs |-> {},
                                                          status |-> "Error"]
                                                 @@ listRequests)
                       /\ pc' = [pc EXCEPT ![self] = "DoListReply"]
                       /\ UNCHANGED << apiState, requests, stack, op, obj, 
                                       kind, shouldReconcile >>

DoListReply(self) == /\ pc[self] = "DoListReply"
                     /\ listRequests[self].status # "Pending"
                     /\ \/ /\ TRUE
                           /\ UNCHANGED listRequests
                        \/ /\ REQUESTS_CAN_TIMEOUT
                           /\ listRequests' = [listRequests EXCEPT ![self].objs = {},
                                                                   ![self].status = "Error"]
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ kind' = [kind EXCEPT ![self] = Head(stack[self]).kind]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << apiState, requests, op, obj, 
                                     shouldReconcile >>

ListAPI(self) == DoListRequest(self) \/ DoListReply(self)

CStart(self) == /\ pc[self] = "CStart"
                /\ \/ /\ shouldReconcile' = [shouldReconcile EXCEPT ![self] = TRUE]
                   \/ /\ TRUE
                      /\ UNCHANGED shouldReconcile
                /\ IF shouldReconcile'[self]
                      THEN /\ /\ obj' = [obj EXCEPT ![self] = [k |-> "Secret", n |-> "foo"]]
                              /\ op' = [op EXCEPT ![self] = "Force"]
                              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "API",
                                                                       pc        |->  "C1",
                                                                       op        |->  op[self],
                                                                       obj       |->  obj[self] ] >>
                                                                   \o stack[self]]
                           /\ pc' = [pc EXCEPT ![self] = "DoRequest"]
                           /\ kind' = kind
                      ELSE /\ /\ kind' = [kind EXCEPT ![self] = "Secret"]
                              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ListAPI",
                                                                       pc        |->  "C3",
                                                                       kind      |->  kind[self] ] >>
                                                                   \o stack[self]]
                           /\ pc' = [pc EXCEPT ![self] = "DoListRequest"]
                           /\ UNCHANGED << op, obj >>
                /\ UNCHANGED << apiState, requests, listRequests >>

C1(self) == /\ pc[self] = "C1"
            /\ IF requests[self].status # "Ok"
                  THEN /\ pc' = [pc EXCEPT ![self] = "CStart"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "C10"]
            /\ UNCHANGED << apiState, requests, listRequests, stack, op, obj, 
                            kind, shouldReconcile >>

C10(self) == /\ pc[self] = "C10"
             /\ /\ obj' = [obj EXCEPT ![self] = [k |-> "PVC", n |-> "mypvc"]]
                /\ op' = [op EXCEPT ![self] = "Force"]
                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "API",
                                                         pc        |->  "C11",
                                                         op        |->  op[self],
                                                         obj       |->  obj[self] ] >>
                                                     \o stack[self]]
             /\ pc' = [pc EXCEPT ![self] = "DoRequest"]
             /\ UNCHANGED << apiState, requests, listRequests, kind, 
                             shouldReconcile >>

C11(self) == /\ pc[self] = "C11"
             /\ IF requests[self].status # "Ok"
                   THEN /\ pc' = [pc EXCEPT ![self] = "CStart"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "c12"]
             /\ UNCHANGED << apiState, requests, listRequests, stack, op, obj, 
                             kind, shouldReconcile >>

c12(self) == /\ pc[self] = "c12"
             /\ /\ obj' = [obj EXCEPT ![self] = [k |-> "PVC", n |-> "mypvc"]]
                /\ op' = [op EXCEPT ![self] = "Get"]
                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "API",
                                                         pc        |->  "C13",
                                                         op        |->  op[self],
                                                         obj       |->  obj[self] ] >>
                                                     \o stack[self]]
             /\ pc' = [pc EXCEPT ![self] = "DoRequest"]
             /\ UNCHANGED << apiState, requests, listRequests, kind, 
                             shouldReconcile >>

C13(self) == /\ pc[self] = "C13"
             /\ IF requests[self].status # "Ok" \/ IsUnboundPVC(requests[self].obj)
                   THEN /\ pc' = [pc EXCEPT ![self] = "CStart"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "C2"]
             /\ UNCHANGED << apiState, requests, listRequests, stack, op, obj, 
                             kind, shouldReconcile >>

C2(self) == /\ pc[self] = "C2"
            /\ shouldReconcile' = [shouldReconcile EXCEPT ![self] = FALSE]
            /\ Assert(ObjectExists([k |-> "Secret", n |-> "foo"]), 
                      "Failure of assertion at line 196, column 9.")
            /\ pc' = [pc EXCEPT ![self] = "C5"]
            /\ UNCHANGED << apiState, requests, listRequests, stack, op, obj, 
                            kind >>

C3(self) == /\ pc[self] = "C3"
            /\ IF listRequests[self].status # "Ok"
                  THEN /\ pc' = [pc EXCEPT ![self] = "CStart"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "C8"]
            /\ UNCHANGED << apiState, requests, listRequests, stack, op, obj, 
                            kind, shouldReconcile >>

C8(self) == /\ pc[self] = "C8"
            /\ IF listRequests[self].objs = {}
                  THEN /\ pc' = [pc EXCEPT ![self] = "C4"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "C6"]
            /\ UNCHANGED << apiState, requests, listRequests, stack, op, obj, 
                            kind, shouldReconcile >>

C6(self) == /\ pc[self] = "C6"
            /\ \E s \in listRequests[self].objs:
                 /\ /\ obj' = [obj EXCEPT ![self] = [k |-> s.k, n |-> s.n]]
                    /\ op' = [op EXCEPT ![self] = "Delete"]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "API",
                                                             pc        |->  "C7",
                                                             op        |->  op[self],
                                                             obj       |->  obj[self] ] >>
                                                         \o stack[self]]
                 /\ pc' = [pc EXCEPT ![self] = "DoRequest"]
            /\ UNCHANGED << apiState, requests, listRequests, kind, 
                            shouldReconcile >>

C7(self) == /\ pc[self] = "C7"
            /\ IF requests[self].status # "Ok" \/ Cardinality(listRequests[self].objs) > 1
                  THEN /\ pc' = [pc EXCEPT ![self] = "CStart"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "C4"]
            /\ UNCHANGED << apiState, requests, listRequests, stack, op, obj, 
                            kind, shouldReconcile >>

C4(self) == /\ pc[self] = "C4"
            /\ Assert(~ObjectExists([k |-> "Secret", n |-> "foo"]), 
                      "Failure of assertion at line 216, column 9.")
            /\ pc' = [pc EXCEPT ![self] = "C5"]
            /\ UNCHANGED << apiState, requests, listRequests, stack, op, obj, 
                            kind, shouldReconcile >>

C5(self) == /\ pc[self] = "C5"
            /\ pc' = [pc EXCEPT ![self] = "CStart"]
            /\ UNCHANGED << apiState, requests, listRequests, stack, op, obj, 
                            kind, shouldReconcile >>

Client(self) == CStart(self) \/ C1(self) \/ C10(self) \/ C11(self)
                   \/ c12(self) \/ C13(self) \/ C2(self) \/ C3(self)
                   \/ C8(self) \/ C6(self) \/ C7(self) \/ C4(self)
                   \/ C5(self)

PVCStart(self) == /\ pc[self] = "PVCStart"
                  /\ /\ kind' = [kind EXCEPT ![self] = "PVC"]
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ListAPI",
                                                              pc        |->  "PVCListedPVCs",
                                                              kind      |->  kind[self] ] >>
                                                          \o stack[self]]
                  /\ pc' = [pc EXCEPT ![self] = "DoListRequest"]
                  /\ UNCHANGED << apiState, requests, listRequests, op, obj, 
                                  shouldReconcile >>

PVCListedPVCs(self) == /\ pc[self] = "PVCListedPVCs"
                       /\ IF \/ listRequests[self].status # "Ok"
                             \/ {o \in listRequests[self].objs: IsUnboundPVC(o)} = {}
                             THEN /\ pc' = [pc EXCEPT ![self] = "PVCStart"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "PVCHavePVCs"]
                       /\ UNCHANGED << apiState, requests, listRequests, stack, 
                                       op, obj, kind, shouldReconcile >>

PVCHavePVCs(self) == /\ pc[self] = "PVCHavePVCs"
                     /\ \E unb \in {o \in listRequests[self].objs: IsUnboundPVC(o)}:
                          LET bound == IF "spec" \notin DOMAIN unb THEN
                                          "spec" :> ("pvname" :> unb.n) @@ unb
                                       ELSE
                                          [unb EXCEPT !.spec = "pvname" :> unb.n @@ @] IN
                            /\ /\ obj' = [obj EXCEPT ![self] = bound]
                               /\ op' = [op EXCEPT ![self] = "Update"]
                               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "API",
                                                                        pc        |->  "PVCDone",
                                                                        op        |->  op[self],
                                                                        obj       |->  obj[self] ] >>
                                                                    \o stack[self]]
                            /\ pc' = [pc EXCEPT ![self] = "DoRequest"]
                     /\ UNCHANGED << apiState, requests, listRequests, kind, 
                                     shouldReconcile >>

PVCDone(self) == /\ pc[self] = "PVCDone"
                 /\ pc' = [pc EXCEPT ![self] = "PVCStart"]
                 /\ UNCHANGED << apiState, requests, listRequests, stack, op, 
                                 obj, kind, shouldReconcile >>

PVCController(self) == PVCStart(self) \/ PVCListedPVCs(self)
                          \/ PVCHavePVCs(self) \/ PVCDone(self)

APIStart(self) == /\ pc[self] = "APIStart"
                  /\ \/ /\ \E c \in PendingClients:
                             IF requests[c].op = "Create"
                                THEN /\ IF \E o \in apiState: IsVersionOf(o, requests[c].obj)
                                           THEN /\ requests' = [requests EXCEPT ![c].status = "Error"]
                                                /\ UNCHANGED apiState
                                           ELSE /\ apiState' = (apiState \cup {Write(requests[c].obj)})
                                                /\ requests' = [requests EXCEPT ![c].status = "Ok"]
                                ELSE /\ IF requests[c].op = "Force"
                                           THEN /\ IF \E o \in apiState: IsVersionOf(o, requests[c].obj)
                                                      THEN /\ apiState' =         {
                                                                          IF IsVersionOf(o, requests[c].obj) THEN
                                                                              Write(requests[c].obj)
                                                                          ELSE
                                                                              o
                                                                          : o \in apiState}
                                                      ELSE /\ apiState' = (apiState \cup {Write(requests[c].obj)})
                                                /\ requests' = [requests EXCEPT ![c].status = "Ok"]
                                           ELSE /\ IF requests[c].op = "Get"
                                                      THEN /\ IF \E o \in apiState: IsVersionOf(o, requests[c].obj)
                                                                 THEN /\ requests' = [requests EXCEPT ![c].obj = CHOOSE o \in apiState:
                                                                                                                  IsVersionOf(o, requests[c].obj),
                                                                                                      ![c].status = "Ok"]
                                                                      /\ apiState' =         {
                                                                                     IF IsVersionOf(o, requests'[c].obj) THEN
                                                                                         Read(o, c)
                                                                                     ELSE
                                                                                         o
                                                                                     : o \in apiState}
                                                                 ELSE /\ requests' = [requests EXCEPT ![c].status = "Error"]
                                                                      /\ UNCHANGED apiState
                                                      ELSE /\ IF requests[c].op = "Delete"
                                                                 THEN /\ apiState' = {o \in apiState: ~IsVersionOf(o, requests[c].obj)}
                                                                      /\ requests' = [requests EXCEPT ![c].status = "Ok"]
                                                                 ELSE /\ IF requests[c].op = "Update"
                                                                            THEN /\ IF \E o \in apiState: (IsVersionOf(o, requests[c].obj) /\ HasRead(o, c))
                                                                                       THEN /\ apiState' = {o \in apiState: ~IsVersionOf(o, requests[c].obj)}
                                                                                                           \cup
                                                                                                           {Write(requests[c].obj)}
                                                                                            /\ requests' = [requests EXCEPT ![c].status = "Ok"]
                                                                                       ELSE /\ requests' = [requests EXCEPT ![c].status = "Error"]
                                                                                            /\ UNCHANGED apiState
                                                                            ELSE /\ Assert(FALSE, 
                                                                                           "Failure of assertion at line 348, column 21.")
                                                                                 /\ UNCHANGED << apiState, 
                                                                                                 requests >>
                        /\ UNCHANGED listRequests
                     \/ /\ \E c \in PendingListClients:
                             /\ listRequests' = [listRequests EXCEPT ![c].objs = {o \in apiState: o.k = listRequests[c].kind},
                                                                     ![c].status = "Ok"]
                             /\ apiState' =         {
                                            IF o.k = listRequests'[c].kind THEN
                                                Read(o, c)
                                            ELSE
                                                o
                                            : o \in apiState}
                        /\ UNCHANGED requests
                  /\ pc' = [pc EXCEPT ![self] = "APIStart"]
                  /\ UNCHANGED << stack, op, obj, kind, shouldReconcile >>

APIServer(self) == APIStart(self)

Next == (\E self \in ProcSet: API(self) \/ ListAPI(self))
           \/ (\E self \in {"Client"}: Client(self))
           \/ (\E self \in {"PVCController"}: PVCController(self))
           \/ (\E self \in {"Server"}: APIServer(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* END TRANSLATION 


-----------------------------------------------------------------------------

(***************************************************************************)
(* Invariant: "Type-checking" of the variables.                            *)
(***************************************************************************)
TypeOK ==
    \* All objects in the API Server are valid (well-formed)
    /\ \A o \in apiState: IsValidAPIObject(o)
    \* All requests are well-formed
    /\ \A c \in DOMAIN requests: IsValidRequest(requests[c])
    /\ \A c \in DOMAIN listRequests: IsValidListRequest(listRequests[c])

(***************************************************************************)
(* Invariant: The API server is only allowed to hold one version of an     *)
(* object at a time.                                                       *)
(***************************************************************************)
OnlyOneVersion ==
    \A o1, o2 \in apiState: \/ o1 = o2
                            \/ ~IsVersionOf(o1, o2)

(***************************************************************************)
(* ReconcileCompletes is a temporal property which guarantees that         *)
(* eventually, we will succeed in reconciling the objects.  It works based *)
(* on the assumption (since we're schedule-based) that the only way for    *)
(* the shouldReconcile variable to become FALSE is for the reconcile to    *)
(* complete successfully.                                                  *)
(***************************************************************************)
ReconcileCompletes ==
    shouldReconcile.Client ~> ~shouldReconcile.Client

(***************************************************************************)
(* CleansUpProperly is a temporal property that says if shouldReconcile    *)
(* remains FALSE, eventually all the listed objects will be deleted from   *)
(* the API server.                                                         *)
(***************************************************************************)
CleansUpProperly ==
    []~shouldReconcile.Client ~>
        \A o \in apiState: /\ ~IsVersionOf(o, [k |-> "Secret", n |-> "foo"])

=============================================================================
\* Modification History
\* Last modified Fri Oct 28 16:39:42 EDT 2022 by jstrunk
\* Created Fri Mar 26 14:54:43 EDT 2021 by jstrunk
