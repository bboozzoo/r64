// The MIT License (MIT)
//
// Copyright (c) 2020 Maciek Borzecki <maciek.borzecki@gmail.com>
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

mod CPU6510 {
    const ADDR_STACK_START: u16 = 0x0100;
    const ADDR_STACK_END: u16 = 0x01ff;

    const ADDR_NMI_VECTOR: u16 = 0xfffa;
    const ADDR_RESET_VECTOR: u16 = 0xfffc;
    const ADDR_IRQ_VECTOR: u16 = 0xfffe;

    // CPU6510 is a model of MOS 6510 Microprocessor.
    // Based on http://archive.6502.org/datasheets/mos_6510_mpu.pdf

    #[derive(Copy, Clone, Default, Debug)]
    struct ProgramCounter {
        // TODO: reduce to single u16?
        PCH: u8,
        PCL: u8,
    }

    impl ProgramCounter {
        fn inc(&mut self) {
            if self.PCL == 0xff {
                self.PCH += 1;
                self.PCL = 0;
            } else {
                self.PCL += 1;
            }
        }

        fn set(&mut self, addr: u16) {
            self.PCL = (addr & 0xff) as u8;
            self.PCH = (addr >> 8) as u8;
        }
    }

    impl From<ProgramCounter> for u16 {
        fn from(pc: ProgramCounter) -> u16 {
            let mut v = (pc.PCH as u16) << 8;
            v = v | (pc.PCL as u16);
            return v;
        }
    }

    #[derive(Copy, Clone, Default, Debug, PartialEq)]
    struct StatusRegister {
        N: bool, // Negative
        V: bool, // Overflow
        B: bool, // BRK command
        D: bool, // Decimal model
        I: bool, // IRQ disable
        Z: bool, // Zero
        C: bool, // Carry
    }

    impl From<StatusRegister> for u8 {
        fn from(sr: StatusRegister) -> u8 {
            0 as u8 |
            (sr.C as u8) << 0 |
            (sr.Z as u8) << 1 |
            (sr.I as u8) << 2 |
            (sr.D as u8) << 3 |
            (sr.B as u8) << 4 |
            // reserved
            (1 << 5) as u8 |
            (sr.V as u8) << 6 |
            (sr.N as u8) << 7
        }
    }

    impl From<u8> for StatusRegister {
        fn from(sr: u8) -> StatusRegister {
            StatusRegister {
                N: (sr & 1 << 7) != 0,
                V: (sr & 1 << 6) != 0,
                B: (sr & 1 << 4) != 0,
                D: (sr & 1 << 3) != 0,
                I: (sr & 1 << 2) != 0,
                Z: (sr & 1 << 1) != 0,
                C: (sr & 1) != 0,
            }
        }
    }

    #[derive(Default)]
    struct Registers {
        A: u8,              // Accumulator
        Y: u8,              // Y index register
        X: u8,              // X index register
        PC: ProgramCounter, // (PCH|PCL) program counter
        S: u8,              // Stack pointer
        P: StatusRegister,  // Processor status register
    }

    enum Instruction {
        ADS, // Add memory to Accumulator with Carry
        AND, // AND memory with Accumulator
        ASL, // Shift left one bit (memory or Accumulator)

        BCC, // Branch on Carry clear
        BCS, // Branch on Carry set
        BEQ, // Branch on result Zero
        BIT, // Test bits in memory with Accumulator
        BMI, // Branch on result Negative
        BNE, // Branch on result not Zero
        BPL, // Branch on result not plus
        BRK, // Force break
        BVC, // Branch on Overflow clear
        BVS, // Branch on Overflow set

        CLC, // Clear carry flag
        CLD, // Clear Decimal mode
        CLI, // Clear Interrupt disable bit
        CLV, // Clear Overflow bit
        CMP, // Compare memory and Accumulator
        CPX, // Compare memory and index X
        CPY, // Compare memory and index Y

        DEC, // Decrement memory by one
        DEX, // Decrement index X by one
        DEY, // Decrement index Y by one

        EOR, // (exclusive OR) XOR memory or Accumulator

        INC, // Increment memory by one
        INX, // Increment index X by one
        INY, // Increment index Y by one

        JMP, // Jump to new location
        JSR, // Jump to new location saving return address

        LDA, // Load Accumulator with memory
        LDX, // Load index X with memory
        LDY, // Load index Y with memory
        LSR, // Shift right one bit (memory or Accumulator)

        NOP, // noop

        ORA, // OR memory with Accumulator

        PHA, // Push Accumulator on Stack
        PHP, // Push processor status on Stack
        PLA, // Pull Accumulator from Stack
        PLP, // Pull processor status from Stack

        ROL, // Rotate one bit left (memory or Accumulator)
        ROR, // Rotate one bit right (memory or Accumulator)
        RTI, // Return from interrupt
        RTS, // Return from subroutine

        SBC, // Subtract memory from Accumulator with Borrow
        SEC, // Set Carry flag
        SED, // Set Decimal flag
        SEI, // Set Interrupt disable flag
        STA, // Store Accumulator in memory
        STX, // Store index X in memory
        STY, // Store index Y in memory

        TAX, // Transfer Accumulator to index X
        TAY, // Transfer Accumulator to index Y
        TSX, // Transfer Stack pointer to index X
        TXA, // Transfer index X to Accumulator
        TXS, // Transfer index X to Stack register
        TYA, // Transfer index Y to Accumulator
    }

    pub struct CPU<'a> {
        r: Registers,

        mem: &'a mut dyn component::Memory<u16, u8>,

        wait : u32,
    }

    use crate::component;

    impl component::Clocked for CPU<'_> {
        fn tick(&mut self) {
            if self.wait > 0 {
                self.wait = self.wait - 1;
            } else {
                self.dispatch_one();
            }
        }
    }

    impl CPU<'_> {
        fn dispatch_one(&mut self) {
            let _ = self.fetch_insn();
        }

        fn fetch_insn(&mut self) -> u8 {
            let insn = self.mem.read(u16::from(self.r.PC));
            self.r.PC.inc();
            return insn;
        }

        fn fetch_addr(&self, addr: u16) -> u16 {
            let mut val = self.mem.read(addr+1) as u16;
            val = val << 8;
            val = val | (self.mem.read(addr) as u16);
            return val;
        }

        fn reset(&mut self) {
            self.r = Default::default();
            self.r.PC.set(self.fetch_addr(ADDR_RESET_VECTOR));
            self.r.S = 0xff;
        }

        // push onto the stack
        fn push(&mut self, data: u8) {
            // TODO: check limits
            self.mem.write(ADDR_STACK_START + (self.r.S as u16), data);
            self.r.S = self.r.S - 1;
        }

        // pop from the stack
        fn pop(&mut self) -> u8 {
            // TODO: check limits
            self.r.S = self.r.S + 1;
            self.mem.read(ADDR_STACK_START + (self.r.S as u16))
        }

        fn op_brk(&mut self) {
            let mut pc = self.r.PC;
            pc.inc();
            self.push(pc.PCH);
            self.push(pc.PCL);
            self.push(u8::from(self.r.P));
            self.r.P.I = true;  // interrupt disable
            self.r.P.B = true;  // BRK command
            self.schedule_wait(7); // 7 cycles
            self.r.PC.set(ADDR_IRQ_VECTOR); // IRQ handler
        }

        fn schedule_wait(&mut self, wait : u32) {
            self.wait = wait;
        }

        fn stall(&self) -> bool {
            self.wait > 0
        }
    }

    pub fn new_with_memory(mem: &mut dyn component::Memory<u16, u8>) -> CPU {
        return CPU {
            r: Default::default(),
            mem: mem,
            wait: 0,
        };
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn pc() {
            let mut pc: ProgramCounter = Default::default();
            for i in 0..300 {
                assert_eq!(u16::from(pc), i);
                pc.inc();
            }
        }

        #[test]
        fn sr_conversion_simple() {
            let mut sr = StatusRegister {
                C: true,
                ..Default::default()
            };
            let v1 = u8::from(sr);
            assert_eq!(v1, 1 << 5 | 0x1);
            let sr2 = StatusRegister::from(v1);
            assert_eq!(sr2, sr);
        }

        #[test]
        fn sr_conversion_more() {
            let mut sr = StatusRegister {
                C: true,
                N: true,
                I: true,
                ..Default::default()
            };
            let v1 = u8::from(sr);
            assert_eq!(v1, 1 << 7 | 1 << 2 | 1 << 5 | 1);
            let sr2 = StatusRegister::from(v1);
            assert_eq!(sr2, sr);
        }

        impl component::Memory<u16, u8> for [u8; 65535] {
            fn read(&self, addr: u16) -> u8 {
                return self[usize::from(addr)];
            }
            fn write(&mut self, addr: u16, data: u8) {
                self[usize::from(addr)] = data;
            }
        }

        #[test]
        fn cpu_simple() {
            let mut mem: [u8; 65535] = [0; 65535];
            let mut cpu = new_with_memory(&mut mem);
            assert_eq!(u16::from(cpu.r.PC), 0);
            cpu.dispatch_one();
            assert_eq!(u16::from(cpu.r.PC), 1);
        }

        #[test]
        fn cpu_reset() {
            let mut mem: [u8; 65535] = [0; 65535];
            let prog_start = ADDR_STACK_END + 1;
            let (lo, hi) = ((prog_start & 0xff), (prog_start >> 8 & 0xff));

            mem[ADDR_RESET_VECTOR as usize] = lo as u8;
            mem[(ADDR_RESET_VECTOR+1) as usize] = hi as u8;

            let mut cpu = new_with_memory(&mut mem);
            cpu.reset();

            assert_eq!(cpu.r.S, 0xff);
            assert_eq!(u8::from(cpu.r.P), 1 << 5);
            assert_eq!(u16::from(cpu.r.PC), ADDR_STACK_END + 1);
        }

        #[test]
        fn op_brk() {
            let mut mem: [u8; 65535] = [0; 65535];
            let mut cpu = new_with_memory(&mut mem);
            cpu.reset();

            cpu.dispatch_one();
        }
}
}
