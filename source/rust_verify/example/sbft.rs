mod pervasive;

mod library {
    #[allow(unused_imports)]
    use {
        builtin::*,
        builtin_macros::*,
        crate::*,   // macros are defined at crate root somehow; need this for set![]
            // TODO(utaal): Need to put set! macro into module namespace for less confusion.
        crate::pervasive::*,
        crate::pervasive::set::*,
        crate::pervasive::map::*,
    };

    #[spec]
    pub fn full_imap<K,V>(im:Map<K,V>) -> bool {
        forall(|k| im.dom().contains(k))
    }
}

// TODO(help): what's the equivalent of a module here?
mod host_identifiers {
    #[allow(unused_imports)]
    use {
        builtin::*,
        builtin_macros::*,
        crate::pervasive::*,
        crate::pervasive::set::*
    };

    fndecl!(pub fn num_hosts() -> int);

    #[proof]
    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    // TODO: Chris is suspicious that this argumentless-forall mightn't work
    pub fn axiom_num_hosts() {
        ensures(num_hosts() > 0);
    }

    // TODO(utaal): The verifier does not yet support the following Rust feature: unsupported item.
    // Sure would be nice to have it.
    //type HostId = int;
    #[derive(PartialEq, Eq, Structural)]
    pub struct HostId { pub value: int }

    #[spec]
    pub fn ValidHostId(h: HostId) -> bool {
        0 <= h.value && h.value < num_hosts()
    }

    #[spec]
    fn AllHosts() -> Set<HostId>
    {
        Set::new(|h: HostId| ValidHostId(h))
            //&& 0<=h.value<num_hosts()  // don't need Dafny's finite-set heuristic
    }
}

mod network {
    #[allow(unused_imports)]
    use {
        builtin::*,
        builtin_macros::*,
        crate::*,   // macros are defined at crate root somehow; need this for set![]
            // TODO(utaal): Need to put set! macro into module namespace for less confusion.
        crate::pervasive::*,
        crate::pervasive::set::*,
        crate::pervasive::option::*,
        crate::host_identifiers::*,
    };
    
    // NB jonh renamed to NetMessage to remedy ambiguity with protocol Message (payload).
    #[derive(PartialEq, Eq, Structural)]
    pub struct NetMessage<Payload> {
        pub sender: HostId,
        pub payload: Payload
    }

    // TODO(design): This is a lot of syntax for 'struct'; looking for brevity.
    //#[derive(PartialEq, Eq, Structural)]
    pub struct MessageOps<Payload>
    {
        pub recv:Option<NetMessage<Payload>>,
        pub send:Option<NetMessage<Payload>>,
        pub signed_msgs_to_check:Set<NetMessage<Payload>>
    }

    impl<Payload> MessageOps<Payload> {
        #[spec]
        pub fn is_send(self) -> bool {
               true
            && self.recv.is_None()
            && self.send.is_Some()
        }

        #[spec]
        pub fn no_send_recv(self) -> bool {
               true
            && self.recv.is_None()
            && self.send.is_None()
        }
    }

    //#[derive(PartialEq, Eq, Structural)]
    // Too bad, Set can't be Structural, so you'll have to .equal().
    pub struct Variables<Payload> {
        sent_msgs: Set<NetMessage<Payload>>
    }

    impl<Payload> Variables<Payload> {
        #[spec]
        pub fn init(v: Variables<Payload>) -> bool {
            equal(v.sent_msgs, set![])
        }

        #[spec]
        pub fn next(v: Variables<Payload>, vp: Variables<Payload>, msg_ops: MessageOps<Payload>, sender: HostId) -> bool {
               true
            // Only allow receipt of a message if we've seen it has been sent.
            && (msg_ops.recv.is_Some() >>= v.sent_msgs.contains(msg_ops.recv.value()))
            // Record the sent message, if there was one.
            && equal(vp.sent_msgs,
                    v.sent_msgs.union(
                        if msg_ops.send.is_Some() && msg_ops.send.value().sender == sender {
                            set![msg_ops.send.value()]
                        } else {
                            set![]
                        }))
            && msg_ops.signed_msgs_to_check.subset_of(v.sent_msgs)
        }
    }
}

mod messages {
    #[allow(unused_imports)]
    use {
        builtin::*,
        builtin_macros::*,
        crate::*,   // macros are defined at crate root somehow; need this for set![]
            // TODO(utaal): Need to put set! macro into module namespace for less confusion.
        crate::pervasive::*,
        crate::pervasive::set::*,
        crate::pervasive::map::*,
        crate::pervasive::option::*,
        crate::library::*,
        crate::host_identifiers::*,
        crate::network::*,
    };

    // TODO(utaal): The verifier does not yet support the following Rust feature: unsupported item
    //type SequenceID = nat;
    #[derive(PartialEq, Eq, Structural)]
    pub struct SequenceID  { pub value: nat }

    // TODO(utaal): The verifier does not yet support the following Rust feature: unsupported item
    //type ViewNum = nat
    #[derive(PartialEq, Eq, Structural)]
    pub struct ViewNum  { pub value: nat }

    pub struct ClientOperation {
        pub sender: HostId,
        pub timestamp: nat
    }

    pub enum OperationWrapper {
        Noop,
        ClientOp { clientOperation: ClientOperation }
    }

    #[spec]
    fn senders_of(msgs: Set<NetMessage<Message>>) -> Set<HostId> {
        msgs.map(|msg: NetMessage<Message>| msg.sender)
    }

    #[spec]
    pub fn unique_senders(msgs: Set<NetMessage<Message>>) -> bool {
        forall(|m1, m2| #[auto_trigger]
                     true
                  && msgs.contains(m1)
                  && msgs.contains(m2)
                  && !equal(m1, m2)
              >>= m1.sender != m2.sender)
    }

    pub struct PreparedCertificate {
        pub votes: Set<NetMessage<Message>>
    }

    impl PreparedCertificate {
        #[spec]
        pub fn prototype(self) -> Message {
            recommends(self.votes.len() > 0);
            choose(|prot| self.votes.contains(prot)).payload
        }

        #[spec]
        pub fn wf(self) -> bool {
            forall(|v| #[auto_trigger] self.votes.contains(v) >>= v.payload.xis_Prepare())
        }

        #[spec]
        pub fn empty(self) -> bool {
            self.votes.len() == 0
        }

        #[spec]
        pub fn valid(self, quorum_size: nat) -> bool {
               false
            || self.empty()
            || (   true
                && self.votes.len() == quorum_size
                && self.wf()
                // messages have to be votes that match eachother by the prototype 
                && forall(|v| #[auto_trigger] self.votes.contains(v) >>= equal(v.payload, self.prototype()))
                && unique_senders(self.votes)
                )
        }
    }

    pub struct ViewChangeMsgsSelectedByPrimary {
        msgs: Set<NetMessage<Message>>
    }

    impl ViewChangeMsgsSelectedByPrimary {
        #[spec]
        pub fn valid(self, view: ViewNum, quorum_size: nat) -> bool {
               true
            && self.msgs.len() > 0
            // All the ViewChange messages have to be for the same View. 
            && forall(|v| #[auto_trigger] self.msgs.contains(v) >>=
                         true
                      && v.payload.xis_ViewChangeMsg()
                      && v.payload.wf()
                      && v.payload.new_view() == view
                      )
            && unique_senders(self.msgs)
            && self.msgs.len() == quorum_size
        }
    }

    // TODO(utaal): Frustrating blocker (see xis_ placeholder methods below)
    //#[is_variant]
    pub enum Message {
        PrePrepare { view: ViewNum, seq_id:SequenceID, operation_wrapper: OperationWrapper },
        Prepare { view: ViewNum, seq_id:SequenceID, operation_wrapper: OperationWrapper },
        Commit { view: ViewNum, seq_id:SequenceID, operation_wrapper: OperationWrapper },
        ClientRequest { client_op: ClientOperation },
        ViewChangeMsg { new_view: ViewNum, certificates: Map<SequenceID, PreparedCertificate> },
        NewViewMsg { new_view: ViewNum, vcMsgs: ViewChangeMsgsSelectedByPrimary },
    }

    impl Message {
        #[spec] pub fn xis_PrePrepare(self) -> bool { true }
        #[spec] pub fn xis_Prepare(self) -> bool { true }
        #[spec] pub fn xis_ClientRequest(self) -> bool { true }
        #[spec] pub fn xis_ViewChangeMsg(self) -> bool { true }
        #[spec] pub fn xis_NewViewMsg(self) -> bool { true }
        // TODO(utaal): Ewww
        #[spec] pub fn new_view(self) -> ViewNum {
            //self.get_ViewChangeMsg_0()
            ViewNum{value: 0}
        }
        #[spec] pub fn certificates(self) -> Map<SequenceID, PreparedCertificate> {
            Map::empty()
            //self.get_ViewChangeMsg_1()
        }
        #[spec] pub fn get_client_op(self) -> ClientOperation {
            ClientOperation { sender: HostId{value: 0}, timestamp: 0 }
        }

        #[spec]
        pub fn wf(self) -> bool {
            self.xis_ViewChangeMsg() >>= full_imap(self.certificates())
        }
    }
}

mod cluster_config {
    #[allow(unused_imports)]
    use {
        builtin::*,
        builtin_macros::*,
        crate::*,   // macros are defined at crate root somehow; need this for set![]
            // TODO(utaal): Need to put set! macro into module namespace for less confusion.
        crate::pervasive::*,
        crate::pervasive::set::*,
        crate::pervasive::option::*,
        crate::host_identifiers::*,
    };

    #[derive(PartialEq, Eq, Structural)]
    pub struct Constants {
        max_byzantine_faulty_replicas: nat,
        num_clients: nat
    }

    impl Constants {
        #[spec]
        pub fn wf(self) -> bool {
               true
            && self.max_byzantine_faulty_replicas > 0 // Require non-trivial BFT system
            && self.num_clients > 0
        }

        #[spec]
        pub fn f(self) -> nat {
            recommends(self.wf());
            self.max_byzantine_faulty_replicas 
        }

        #[spec]
        pub fn n(self) -> nat {
            recommends(self.wf());
            3 * self.f() + 1
        }

        #[spec]
        pub fn cluster_size(self) -> nat {
            recommends(self.wf());
            self.n() + self.num_clients
        }

        #[spec]
        pub fn byzantine_safe_quorum(self) -> nat {
            recommends(self.wf());
            3 * self.f() + 1
        }

        #[spec]
        pub fn agreement_quorum(self) -> nat {
            recommends(self.wf());
            2 * self.f() + 1
        }

        #[spec]
        pub fn is_honest_replica(self, id: HostId) -> bool {
            recommends(self.wf());
               true
            && ValidHostId(id)
            && self.f() <= id.value
            && id.value < self.n()
        }

        #[spec]
        pub fn is_faultyReplica(self, id: HostId) -> bool {
            recommends(self.wf());
               true
            && ValidHostId(id)
            && 0 <= id.value
            && id.value < self.f()
        }

        #[spec]
        pub fn is_replica(self, id: HostId) -> bool {
            recommends(self.wf());
               true
            && ValidHostId(id)
            && 0 <= id.value
            && id.value < self.n()
        }

        #[spec]
        pub fn is_client(self, id: HostId) -> bool {
            recommends(self.wf());
               true
            && ValidHostId(id)
            && self.n() <= id.value
            && id.value < num_hosts()
        }
    }
}

mod client {
    #[allow(unused_imports)]
    use {
        builtin::*,
        builtin_macros::*,
        crate::*,   // macros are defined at crate root somehow; need this for set![]
            // TODO(utaal): Need to put set! macro into module namespace for less confusion.
        crate::pervasive::*,
        crate::pervasive::set::*,
        crate::pervasive::option::*,
        crate::host_identifiers::*,
        crate::messages::*,
    };

    #[derive(PartialEq, Eq, Structural)]
    pub struct Constants {
        my_id: HostId,
        cluster_config: cluster_config::Constants
    }

    impl Constants {
        #[spec]
        pub fn wf(self) -> bool {
               true
            && self.cluster_config.wf()
            && self.cluster_config.is_client(self.my_id)    // NB: jonh upgraded to symbolic name
        }

        #[spec]
        pub fn configure(self, id: HostId, cluster_config: cluster_config::Constants) -> bool {
               true
            && self.my_id == id
            && self.cluster_config == cluster_config
        }
    }

    // Placeholder for possible client state
    #[derive(PartialEq, Eq, Structural)]
    pub struct Variables {
        last_request_timestamp: nat,
        last_reply_timestamp: nat
    }

    impl Variables {
        #[spec]
        pub fn wf(self, c: Constants) -> bool {
               true
            && c.wf()
            && self.last_request_timestamp >= self.last_reply_timestamp
        }
    }
    
    #[spec]
    pub fn pending_requests(c: Constants, v: Variables) -> nat {
        recommends(v.wf(c));
        v.last_request_timestamp - v.last_reply_timestamp
    }

    #[spec]
    pub fn send_client_operation(c: Constants, v: Variables, vp: Variables, msg_ops: network::MessageOps<Message>) -> bool {
        let msg = msg_ops.send.value();
           true
        && v.wf(c)
        && msg_ops.is_send()
        && pending_requests(c, v) == 0
        && msg.payload.xis_ClientRequest()
        && msg.sender == c.my_id
        && msg.payload.get_client_op().sender == c.my_id
        && msg.payload.get_client_op().timestamp == v.last_request_timestamp + 1
        && vp == Variables {
            last_request_timestamp: v.last_request_timestamp + 1,
            ..vp }
        // ...
    }
    
    #[spec]
    pub fn init(c: Constants, v: Variables) -> bool {
           true
        && v.wf(c)
        && v.last_request_timestamp == 0
        && v.last_reply_timestamp == 0
    }

    pub enum Step {
        SendClientOperationStep()
    }

    #[spec]
    pub fn next_step(c: Constants, v: Variables, vp: Variables, msg_ops: network::MessageOps<Message>, step: Step) -> bool {
        match step {
            Step::SendClientOperationStep() => send_client_operation(c, v, vp, msg_ops)
        }
    }

    #[spec]
    pub fn next(c: Constants, v: Variables, vp: Variables, msg_ops: network::MessageOps<Message>) -> bool {
        exists(|step| next_step(c, v, vp, msg_ops, step))
    }
}

mod replica {
    #[allow(unused_imports)]
    use {
        builtin::*,
        builtin_macros::*,
        crate::*,   // macros are defined at crate root somehow; need this for set![]
            // TODO(utaal): Need to put set! macro into module namespace for less confusion.
        crate::pervasive::*,
        crate::pervasive::set::*,
        crate::pervasive::option::*,
        crate::library::*,
        crate::host_identifiers::*,
        crate::messages::*,
        crate::pervasive::map::*,
    };

    pub struct Constants {
        my_id: HostId,
        cluster_config: cluster_config::Constants
    }

    impl Constants {
        #[spec]
        pub fn wf(self) -> bool {
               true
            && self.cluster_config.wf()
            && self.cluster_config.is_replica(self.my_id)
        }

        #[spec] pub fn configure(self, id: HostId, cluster_conf: cluster_config::Constants) -> bool {
               true
            && self.my_id == id
            && self.cluster_config == cluster_conf
        }
    }

    struct ViewChangeMsgs { msgs: Set<network::NetMessage<Message>> }
    impl ViewChangeMsgs {
        #[spec] fn wf(self, c: Constants) -> bool {
               true
            && c.wf()
            && forall(|msg| #[auto_trigger] self.msgs.contains(msg) >>=
                     true
                  && msg.payload.xis_ViewChangeMsg()
                  && c.cluster_config.is_replica(msg.sender))
        }
    }

    struct NewViewMsgs { msgs: Set<network::NetMessage<Message>> }
    impl NewViewMsgs {
        #[spec] fn wf(self, c: Constants) -> bool {
               true
            && c.wf()
            && forall(|msg| #[auto_trigger] self.msgs.contains(msg) >>=
                     true
                  && msg.payload.xis_NewViewMsg()
                  && c.cluster_config.is_replica(msg.sender))
        }
    }

    

    // TODO(utaal): The verifier does not yet support the following Rust feature: unsupported item
    //type PrepareProofSet = Map<HostId, NetMessage<Message>>
    // TODO(utaal): Maps can't Structural, either.
    //#[derive(PartialEq, Eq, Structural)]
    struct PrepareProofSet {
        map: Map<HostId, network::NetMessage<Message>>
    }

    impl PrepareProofSet {
        #[spec]
        pub fn wf(self, c: Constants) -> bool {
            // TODO(utual): index(x) ==> [x]
            forall(|x| #[auto_trigger]
                   true
                && self.map.contains(x)
                && c.cluster_config.is_replica(self.map.index(x).sender))
        }
    }

    //type PrepareProofSet = Map<HostId, NetMessage<Message>>
    // TODO(utaal): Maps can't Structural, either.
    //#[derive(PartialEq, Eq, Structural)]
    struct CommitProofSet {
        map: Map<HostId, network::NetMessage<Message>>
    }

    impl CommitProofSet {
        #[spec]
        pub fn wf(self, c: Constants) -> bool {
            // TODO(utual): index(x) ==> [x]
            forall(|x| #[auto_trigger]
                   true
                && self.map.contains(x)
                && c.cluster_config.is_replica(self.map.index(x).sender))
        }
    }

    //type PrePreparesRecvd = Map<SequenceID, Option<network::NetMessage<Message>>>
    // TODO(utaal): Maps can't Structural, either.
    struct PrePreparesRcvd {
        map: Map<SequenceID, Option<network::NetMessage<Message>>>
    }

    impl PrePreparesRcvd {
        #[spec] pub fn wf(self) -> bool {
               true
            && full_imap(self.map)
            && forall(|x| #[auto_trigger]
                      self.map.contains(x) && self.map.index(x).is_Some()
                      >>= self.map.index(x).value().payload.xis_PrePrepare())
        }
    }

    struct WorkingWindow {
        committed_client_operations: Map<SequenceID, Option<OperationWrapper>>,
        pre_prepares_rcvd: PrePreparesRcvd,
        prepares_rcvd: Map<SequenceID, PrepareProofSet>,
        commits_rcvd: Map<SequenceID, CommitProofSet>,
    }

    // TODO(chris): Discussion: I'm needing auto_trigger on EVERY forall. Is that expected?
    // Is it a sign that I'm an idiot? Will this be why this proof is so timeout-prone?
    impl WorkingWindow {
        #[spec] pub fn wf(self, c: Constants) -> bool {
               true
            && full_imap(self.committed_client_operations)
            && full_imap(self.prepares_rcvd)
            && full_imap(self.commits_rcvd)
            && self.pre_prepares_rcvd.wf()
            && forall(|seqID| #[auto_trigger] self.prepares_rcvd.contains(seqID) >>= self.prepares_rcvd.index(seqID).wf(c))
            && forall(|seqID| #[auto_trigger] self.commits_rcvd.contains(seqID) >>= self.commits_rcvd.index(seqID).wf(c))
        }
    }
}

mod distributed_system {
    #[allow(unused_imports)]
    use {
        builtin::*,
        builtin_macros::*,
        crate::*,   // macros are defined at crate root somehow; need this for set![]
            // TODO(utaal): Need to put set! macro into module namespace for less confusion.
        crate::pervasive::*,
        crate::pervasive::set::*,
        crate::pervasive::option::*,
        crate::library::*,
        crate::host_identifiers::*,
        crate::messages::*,
    };

    pub enum HostConstants {
        Foo
//        Replica { replica_constants: Replica
//        max_byzantine_faulty_replicas: nat,
//        num_clients: nat
    }
}

fn main() {}
