mod pervasive;

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

    // TODO(utaal): The verifier does not yet support the following Rust feature: unsupported item
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
        recv:Option<NetMessage<Payload>>,
        send:Option<NetMessage<Payload>>,
        signed_msgs_to_check:Set<NetMessage<Payload>>
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
        crate::pervasive::option::*,
        crate::host_identifiers::*,
        crate::network::*,
    };

    // TODO(utaal): The verifier does not yet support the following Rust feature: unsupported item
    //type SequenceId = nat;
    #[derive(PartialEq, Eq, Structural)]
    pub struct SequenceID  { pub value: nat }
    pub struct ViewNum  { pub value: nat }

    pub struct ClientOperation { sender: HostId, timestamp: nat }

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
        && forall(|m1, m2| #[auto_trigger]
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
            && forall(|v| self.msgs.contains(v) >>=
                         true
                      && v.payload.is_ViewChangeMsg()
                      && v.payload.wf()
                      && v.payload.newView == view
                      )
            && unique_senders(self.votes)
        }
    }

    //#[is_variant]
    pub enum Message {
        PrePrepare { view: ViewNum, seq_id:SequenceID, operation_wrapper: OperationWrapper },
        Prepare { view: ViewNum, seq_id:SequenceID, operation_wrapper: OperationWrapper }
    }

    impl Message {
        #[spec]
        pub fn xis_Prepare(self) -> bool {
            // self.is_Prepare()
            true    // TODO can't get is_variant to work
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
           true
        && v.wf(c)
        && msg_ops.is_send()
        // ...
    }
}

fn main() {}
