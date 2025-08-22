A collection of collections

* [Documentation](https://stratagyn.github.io/bit-byte-bit)

## Currently Implemented Collections

* [`ContextManager`](stratagyn.github.io/colliflower/context-manager) -- treats a collection of hash maps as one
* [`Stack`](stratagyn.github.io/colliflower/stack) -- a last-in-first out data structure

---

```rust
use bit_byte_bit::Bits;

fn main() {
    let mut bits = bits![0x0A, 0x0B, 0x0C];

    assert_eq!(bits, Bits::new([0x0A, 0x0B, 0x0C]));
    assert_eq!(bits.len(), 24);

    assert_eq!(bits.i(0), 0);
    assert_eq!(bits.i(1), 1);

    bits.set(0);
    bits.reset(1);

    assert_eq!(bits.i(0), 1);
    assert_eq!(bits.i(1), 0);

    bits.toggle(0);

    assert_eq!(bits.i(0), 0);
    assert_eq!(bits.byte(0), 0x8);

    let x = Bits::new([0x20, 0x30, 0x40]);
    let y = Bits::new([0xA0, 0xB0, 0xC0]);

    assert_eq!(x.and(&y), Bits::new([0x20, 0x30, 0x40]));
    assert_eq!(x.complement(), Bits::new([0xDF, 0xCF, 0xBF]));
    assert_eq!(x.or(&y), Bits::new([0xA0, 0xB0, 0xC0]));
    assert_eq!(x.xor(&y), Bits::new([0x80, 0x80, 0x80]));

    let bits = Bits::from([0x0A, 0x0B, 0x0C]);

    assert_eq!(bits.len(), 20);
    assert_eq!(bits.shifted_left(17), Bits::slice(&[0x00, 0x00, 0x04], 20));
    assert_eq!(bits.shifted_right(17), Bits::slice(&[0x06, 0x00, 0x00], 20));
    assert_eq!(bits.rotated_left(4), Bits::slice(&[0xAC, 0xB0, 0x00], 20));
    assert_eq!(bits.rotated_right(4), Bits::slice(&[0xB0, 0xC0, 0x0A], 20));

    let mut ones = 0;

    for bit in bits.iter() { if bit == 1 { ones += 1; } }

    assert_eq!(ones, 7);

    ones = 0;

    for bit in x.iter_from(13) { if bit == 1 { ones += 1; } }

    assert_eq!(ones, 2);

    let mut bytes = x.bytes().iter();

    assert_eq!(bytes.next(), Some(&0x0A));
}
```