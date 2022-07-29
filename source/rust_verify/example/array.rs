
mod pervasive;
use pervasive::{*,seq::*};
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

macro_rules! define_array_type {
    ($name: ident, $n: expr, $type: tt) => (
        seq_macro::seq!(N in 0..$n {

            pub struct $name {
                // Expands to Variant64, Variant65, ...
                #(
                    val_~N: $type,
                )*
            }
            impl Clone for $name {
                #[verifier(external_body)]
                fn clone(&self) -> Self {
                    $name{
                        #(
                            val_~N: self.val_~N,
                        )*
                    }
                }
            }
            verus!{
            impl $name{
                // self.view == self@
                pub spec fn view(&self) -> Seq<$type>;

                #[verifier(external_body)]
                #[verifier(autoview)]
                pub fn index(&self, i: usize) -> (r: &$type)
                ensures
                    *r === self[i],
                {
                    let mut res: &$type = &self.val_0;
                    #(
                        if(i == N) {res = &self.val_~N;}
                    )*
                    res
                }

                #[verifier(external_body)]
                pub fn set(&mut self, i: usize, val: $type)
                ensures
                    self@ === old(self)@.update(i as int, val),
                    self[i] === val,
                    forall(|k: usize| k!=i ==> self[k] === old(self)[k])
                {
                    #(
                        if(i == N) {self.val_~N = val;}
                    )*
                }

                // Define index access in spec
                #[verifier(inline)]
                pub open spec fn spec_index(self, i: usize) -> $type {
                    self@[i]
                }

            }
            }
        });
    )
}

#[repr(C)]
#[repr(packed)]
#[derive(Structural, Copy, PartialEq, Eq)]
pub struct E820Entry {
    pub addr: u64,
    pub size: u64,
    pub memtype: u32,
}

impl Clone for E820Entry {
    #[verifier(external_body)]
    fn clone(&self) -> Self {
        E820Entry {
            addr: self.addr,
            size: self.size,
            memtype: self.memtype,
        }
    }
}


define_array_type!(Array0x50, 10, u64);
define_array_type!(Array0x70, 14, u64);
define_array_type!(Array0x11c, 71, u32);
define_array_type!(Array0xe0, 28, u64);
define_array_type!(Array0x7, 7, u8);
define_array_type!(E820Table, 16, E820Entry);
define_array_type!(E820Table, 16, E820Entry);


#[repr(packed)]
#[repr(C)]
pub struct BootParams {
    pub _pad0: Array0x70,
    pub acpi_rsdp_addr: u64, /* 0x070 */
    pub _pad1: Array0x50,
    pub _ext_cmd_line_ptr: u32, /* 0xc8 */
    pub _pad2: Array0x11c,
    pub e820_entries: u8, /* 0x1e8 */
    pub _pad3: Array0xe0,
    pub _pad4: Array0x7,
    pub e820_table: E820Table, /* 0x2d0 */
}

seq_macro::seq!(N in 0..16 {

        impl BootParams{
            verus! {
        
            pub open spec fn order_e820(&self, i:usize) -> bool {
                &&& self.e820_table[add(i, 1)].addr > (self.e820_table[i].addr + self.e820_table[i].size)
            }
        
            pub open spec fn valid_e820_entry(&self, i:usize) -> bool {
                &&& self.e820_table[i].addr <= 0xffff_ffff_ffff_f000
                &&& self.e820_table[i].size <= 0xffff_ffff_ffff_f000 - self.e820_table[i].addr
            }
        
            pub open spec fn is_ordered_e820(&self) -> bool {
                &&& self.e820_entries < 16
                // TODO(ziqiao): understand why the forall statement does not work
                //&&& forall(|i:usize| (self.order_e820(i) ||| i > self.e820_entries))
                #(
                    &&& (self.order_e820(N) ||| N > self.e820_entries)
                    &&& self.valid_e820_entry(N)
                )*
        
            }
        
            }
        }
});

verus!{

#[proof]
pub fn test_bootparam_get(index1: usize, index2:usize, boot_params: BootParams)
requires
    index2 < index1,
    index1 < boot_params.e820_entries,
    boot_params.is_ordered_e820(),
ensures
    boot_params.e820_table[index1].addr >= boot_params.e820_table[index2].addr
{
}
}

pub fn main(){

} 