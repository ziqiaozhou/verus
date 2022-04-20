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
    
    #[derive(PartialEq, Eq, Structural)]
    pub struct Message<Payload> {
        sender: HostId,
        payload: Payload
    }

    // TODO(design): This is a lot of syntax for 'struct'; looking for brevity.
    //#[derive(PartialEq, Eq, Structural)]
    pub struct MessageOps<Payload>
    {
        recv:Option<Message<Payload>>,
        send:Option<Message<Payload>>,
        signed_msgs_to_check:Set<Message<Payload>>
    }

    impl<Payload> MessageOps<Payload> {
        #[spec]
        fn is_send(self) -> bool {
               true
            && self.recv.is_None()
            && self.send.is_Some()
        }

        #[spec]
        fn no_send_recv(self) -> bool {
               true
            && self.recv.is_None()
            && self.send.is_None()
        }
    }

    //#[derive(PartialEq, Eq, Structural)]
    // Too bad, Set can't be Structural, so you'll have to .equal().
    pub struct Variables<Payload> {
        sent_msgs: Set<Message<Payload>>
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

    pub struct Constants {
        max_byzantine_faulty_replicas: nat,
        num_clients: nat
    }

    impl Constants {
        #[spec]
        pub fn WF(self) -> bool {
               true
            && self.max_byzantine_faulty_replicas > 0 // Require non-trivial BFT system
            && self.num_clients > 0
        }

        #[spec]
        pub fn f(self) -> nat {
            recommends(self.WF());
            self.max_byzantine_faulty_replicas 
        }

        #[spec]
        pub fn n(self) -> nat {
            recommends(self.WF());
            3 * self.f() + 1
        }

        #[spec]
        pub fn cluster_size(self) -> nat {
            recommends(self.WF());
            self.n() + self.num_clients
        }

        #[spec]
        pub fn byzantine_safe_quorum(self) -> nat {
            recommends(self.WF());
            3 * self.f() + 1
        }

        #[spec]
        pub fn agreement_quorum(self) -> nat {
            recommends(self.WF());
            2 * self.f() + 1
        }

        #[spec]
        pub fn is_honest_replica(self, id: HostId) -> bool {
            recommends(self.WF());
               true
            && ValidHostId(id)
            && self.f() <= id.value
            && id.value < self.n()
        }

        #[spec]
        pub fn is_faultyReplica(self, id: HostId) -> bool {
            recommends(self.WF());
               true
            && ValidHostId(id)
            && 0 <= id.value
            && id.value < self.f()
        }

        #[spec]
        pub fn is_replica(self, id: HostId) -> bool {
            recommends(self.WF());
               true
            && ValidHostId(id)
            && 0 <= id.value
            && id.value < self.n()
        }

        #[spec]
        pub fn is_client(self, id: HostId) -> bool {
            recommends(self.WF());
               true
            && ValidHostId(id)
            && self.n() <= id.value
            && id.value < num_hosts()
        }
    }

}

fn main() {}
