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

// #![feature(trace_macros)]
// trace_macros!(true);

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

    enum DecodeInstructionResult {
        Instruction {
            op: Opcode,
            size: usize,
            wait: usize,
            handler: Handler,
        },
        Illegal(u8),
    }

    enum Opcode {
        // Add memory to Accumulator with Carry
        ADC_imm,
        ADC_zp,
        ADC_zpX,
        ADC_abs,
        ADC_absX,
        ADC_absY,
        ADC_indX,
        ADC_indY,
        // AND memory with Accumulator
        AND_imm,
        AND_zp,
        AND_zpX,
        AND_abs,
        AND_absX,
        AND_absY,
        AND_indX,
        AND_indY,
        // ASL Shift left one bit (memory or Accumulator)
        ASL,
        ASL_zp,
        ASL_zpX,
        ASL_abs,
        ASL_absX,
        // BCC Branch on Carry clear
        BCC,
        // BCS Branch on Carry set
        BCS,
        // BEQ Branch on result Zero
        BEQ,
        // BIT Test bits in memory with Accumulator
        BIT_zp,
        BIT_abs,
        // BMI Branch on result Negative
        BMI,
        // BNE Branch on result not Zero
        BNE,
        // BPL Branch on result not plus
        BPL,
        // Force break
        BRK,
        // BVC Branch on Overflow clear
        BVC,
        // BVS Branch on Overflow set
        BVS,
        // CLC Clear carry flag
        CLC,
        // CLD Clear Decimal mode
        CLD,
        // CLI Clear Interrupt disable bit
        CLI,
        // CLV Clear Overflow bit
        CLV,
        // CMP Compare memory and Accumulator
        CMP_imm,
        CMP_zp,
        CMP_zpX,
        CMP_abs,
        CMP_absX,
        CMP_absY,
        CMP_indX,
        CMP_indY,
        // CPX Compare memory and index X
        CPX_imm,
        CPX_zp,
        CPX_abs,
        // CPY Compare memory and index Y
        CPY_imm,
        CPY_zp,
        CPY_abs,
        // DEC Decrement memory by one
        DEC_zp,
        DEC_zpX,
        DEC_abs,
        DEC_absX,
        // DEX Decrement index X by one
        DEX,
        // DEY Decrement index Y by one
        DEY,
        // EOR XOR memory or Accumulator
        EOR_imm,
        EOR_zp,
        EOR_zpX,
        EOR_abs,
        EOR_absX,
        EOR_absY,
        EOR_indX,
        EOR_indY,
        // INC Increment memory by one
        INC_zp,
        INC_zpX,
        INC_abs,
        INC_absX,
        // INX Increment index X by one
        INX,
        // INY Increment index Y by one
        INY,
        // JMP Jump to new location
        JMP_abs,
        JPM_ind,
        // JSR Jump to new location saving return address
        JSR,
        // LDA Load Accumulator with memory
        LDA_imm,
        LDA_zp,
        LDA_zpX,
        LDA_abs,
        LDA_absX,
        LDA_absY,
        LDA_indX,
        LDA_indY,
        // LDX Load index X with memory
        LDX_imm,
        LDX_zp,
        LDX_zpY,
        LDX_abs,
        LDX_absY,
        // LDY Load index Y with memory
        LDY_imm,
        LDY_zp,
        LDY_zpX,
        LDY_abs,
        LDY_absX,
        // LSR Shift right one bit (memory or Accumulator)
        LSR,
        LSR_zp,
        LSR_zpX,
        LSR_abs,
        LSR_absX,
        // noop
        NOP,
        // ORA OR memory with Accumulator
        ORA_imm,
        ORA_zp,
        ORA_zpX,
        ORA_abs,
        ORA_absX,
        ORA_absY,
        ORA_indX,
        ORA_indY,
        // PHA Push Accumulator on Stack
        PHA,
        // PHP Push processor status on Stack
        PHP,
        // PLA Pull Accumulator from Stack
        PLA,
        // PLP Pull processor status from Stack
        PLP,
        // ROL Rotate one bit left (memory or Accumulator)
        ROL,
        ROL_zp,
        ROL_zpX,
        ROL_abs,
        ROL_absX,
        // ROR Rotate one bit right (memory or Accumulator)
        ROR,
        ROR_zp,
        ROR_zpX,
        ROR_abs,
        ROR_absX,
        // RTI Return from interrupt
        RTI,
        // RTS Return from subroutine
        RTS,
        // SBC Subtract memory from Accumulator with Borrow
        SBC_imm,
        SBC_zp,
        SBC_zpX,
        SBC_abs,
        SBC_absX,
        SBC_absY,
        SBC_indX,
        SBC_indY,
        // SEC Set Carry flag
        SEC,
        // SED Set Decimal flag
        SED,
        // SEI Set Interrupt disable flag
        SEI,
        // STA Store Accumulator in memory
        STA_zp,
        STA_zpX,
        STA_abs,
        STA_absX,
        STA_absY,
        STA_indX,
        STA_indY,
        // STX Store index X in memory
        STX_zp,
        STX_zpY,
        STX_abs,
        // STY Store index Y in memory
        STY_zp,
        STY_zpX,
        STY_abs,
        // TAX Transfer Accumulator to index X
        TAX,
        // TAY Transfer Accumulator to index Y
        TAY,
        // TSX Transfer Stack pointer to index X
        TSX,
        // TXA Transfer index X to Accumulator
        TXA,
        // TXS Transfer index X to Stack register
        TXS,
        // TYA Transfer index Y to Accumulator
        TYA,
        // everything else
        Illegal(u8),
    }

    type Handler = fn(&mut CPU, Opcode, &mut Memory);

    pub struct CPU {
        r: Registers,

        wait: u32,
    }

    use crate::component;

    impl component::Clocked for CPU {
        fn tick(&mut self) {
            if self.wait > 0 {
                self.wait = self.wait - 1;
            }
        }
    }

    type Memory = dyn component::Memory<u16, u8>;

    fn decode_ins(ins: u8) -> DecodeInstructionResult {
        macro_rules! ins {
            ($what:tt) => {
                DecodeInstructionResult::Instruction$what
            };
            ($opc:ident, $size:literal, $wait: literal, $handler:expr) => {
                DecodeInstructionResult::Instruction {
                    op: Opcode::$opc,
                    size: $size,
                    wait: $wait,
                    handler: $handler,
                }
            };
        }

        match ins {
            0x00 => ins!(BRK, 1, 7, CPU::op_brk),

            0x69 => ins!(ADC_imm, 2, 2, CPU::op_adc),
            0x65 => ins!(ADC_zp, 2, 3, CPU::op_adc),
            0x75 => ins!(ADC_zpX, 2, 4, CPU::op_adc),
            0x6d => ins!(ADC_abs, 3, 4, CPU::op_adc),
            0x7d => ins!(ADC_absX, 3, 4, CPU::op_adc),
            0x79 => ins!(ADC_absY, 3, 4, CPU::op_adc),
            0x61 => ins!(ADC_indX, 2, 6, CPU::op_adc),
            0x71 => ins!(ADC_indY, 2, 5, CPU::op_adc),

            0x29 => ins!(AND_imm, 2, 2, CPU::op_and),
            0x25 => ins!(AND_zp, 2, 3, CPU::op_and),
            0x35 => ins!(AND_zpX, 2, 4, CPU::op_and),
            0x2d => ins!(AND_abs, 3, 4, CPU::op_and),
            0x3d => ins!(AND_absX, 3, 4, CPU::op_and),
            0x39 => ins!(AND_absY, 3, 4, CPU::op_and),
            0x21 => ins!(AND_indX, 2, 6, CPU::op_and),
            0x31 => ins!(AND_indY, 2, 5, CPU::op_and),

            0x18 => ins!(CLC, 1, 2, CPU::op_clc),
            0xd8 => ins!(CLD, 1, 2, CPU::op_cld),
            0x58 => ins!(CLI, 1, 2, CPU::op_cli),
            0xb8 => ins!(CLV, 1, 2, CPU::op_clv),

            0xe8 => ins!(INX, 1, 2, CPU::op_inx),
            0xc8 => ins!(INY, 1, 2, CPU::op_iny),

            0xea => ins!(NOP, 1, 1, CPU::op_nop),

            0x38 => ins!(SEC, 1, 2, CPU::op_sec),
            0xf8 => ins!(SED, 1, 2, CPU::op_sed),
            0x78 => ins!(SEI, 1, 2, CPU::op_sei),

            _ => DecodeInstructionResult::Illegal(ins),
        }
    }

    impl CPU {
        fn new() -> CPU {
            return CPU {
                r: Default::default(),
                wait: 0,
            };
        }

        fn invoke_for(&mut self, mem: &mut Memory) {
            self.dispatch_one(mem)
        }

        fn dispatch_one(&mut self, mem: &mut Memory) {
            let ins = self.fetch_insn(mem);
            match decode_ins(ins) {
                DecodeInstructionResult::Instruction {
                    op,
                    size,
                    wait,
                    handler,
                } => {
                    handler(self, op, mem);
                }
                DecodeInstructionResult::Illegal(op) => {
                    panic!("illegal op: {}", op);
                }
            }
        }

        fn fetch_insn(&mut self, mem: &Memory) -> u8 {
            let insn = mem.read(u16::from(self.r.PC));
            self.r.PC.inc();
            return insn;
        }

        fn fetch_addr(&self, addr: u16, mem: &Memory) -> u16 {
            let mut val = mem.read(addr + 1) as u16;
            val = val << 8;
            val = val | (mem.read(addr) as u16);
            return val;
        }

        fn reset(&mut self, mem: &Memory) {
            self.r = Default::default();
            self.r.PC.set(self.fetch_addr(ADDR_RESET_VECTOR, mem));
            self.r.S = 0xff;
        }

        // push onto the stack
        fn push(&mut self, data: u8, mem: &mut Memory) {
            // TODO: check limits
            mem.write(ADDR_STACK_START + (self.r.S as u16), data);
            self.r.S = self.r.S - 1;
        }

        // pop from the stack
        fn pop(&mut self, mem: &Memory) -> u8 {
            // TODO: check limits
            self.r.S = self.r.S + 1;
            mem.read(ADDR_STACK_START + (self.r.S as u16))
        }

        fn pop_addr(&mut self, mem: &Memory) -> u16 {
            let low = self.pop(mem);
            let high = self.pop(mem);

            (high as u16) << 8 | low as u16
        }

        fn schedule_wait(&mut self, wait: u32) {
            self.wait = wait;
        }

        fn stall(&self) -> bool {
            self.wait > 0
        }

        fn op_brk(&mut self, _: Opcode, mem: &mut Memory) {
            let mut pc = self.r.PC;
            pc.inc();
            self.push(pc.PCH, mem);
            self.push(pc.PCL, mem);
            self.push(u8::from(self.r.P), mem);
            self.r.P.I = true; // interrupt disable
            self.r.P.B = true; // BRK command
            self.schedule_wait(7); // 7 cycles
            self.r.PC.set(ADDR_IRQ_VECTOR); // IRQ handler
        }

        fn op_nop(&mut self, _: Opcode, mem: &mut Memory) {
            // nop
        }

        fn op_adc(&mut self, op: Opcode, mem: &mut Memory) {

        }
        fn op_and(&mut self, op: Opcode, mem: &mut Memory) {}

        fn op_illegal(&mut self, mem: &mut Memory) {
            panic!("illegal");
        }
        fn op_inx(&mut self, op: Opcode, mem: &mut Memory) {
            self.r.X += 1;
        }
        fn op_iny(&mut self, op: Opcode, mem: &mut Memory) {
            self.r.Y += 1;
        }


        fn op_clc(&mut self, op: Opcode, mem: &mut Memory) {
            self.r.P.C = false;
        }
        fn op_cld(&mut self, op: Opcode, mem: &mut Memory) {
            self.r.P.D = false;
        }
        fn op_cli(&mut self, op: Opcode, mem: &mut Memory) {
            self.r.P.I = false;
        }
        fn op_clv(&mut self, op: Opcode, mem: &mut Memory) {
            self.r.P.V = false;
        }

        fn op_sec(&mut self, op: Opcode, mem: &mut Memory) {
            self.r.P.C = true;
        }
        fn op_sed(&mut self, op: Opcode, mem: &mut Memory) {
            self.r.P.D = true;
        }
        fn op_sei(&mut self, op: Opcode, mem: &mut Memory) {
            self.r.P.I = true;
        }
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
            let mut mem = &mut [0 as u8; 65535] as &mut dyn component::Memory<u16, u8>;
            let mut cpu = CPU::new();
            // NOP
            mem.write(0, 0xea);
            mem.write(ADDR_RESET_VECTOR, 0x0);
            cpu.reset(mem);
            assert_eq!(u16::from(cpu.r.PC), 0);
            cpu.dispatch_one(mem);
            assert_eq!(u16::from(cpu.r.PC), 1);
        }

        #[test]
        fn cpu_reset() {
            let mut mem: [u8; 65535] = [0; 65535];
            let prog_start = ADDR_STACK_END + 1;
            let (lo, hi) = ((prog_start & 0xff), (prog_start >> 8 & 0xff));

            mem[ADDR_RESET_VECTOR as usize] = lo as u8;
            mem[(ADDR_RESET_VECTOR + 1) as usize] = hi as u8;

            let mut cpu = CPU::new();
            cpu.reset(&mem);

            assert_eq!(cpu.r.S, 0xff);
            assert_eq!(u8::from(cpu.r.P), 1 << 5);
            assert_eq!(u16::from(cpu.r.PC), ADDR_STACK_END + 1);
        }

        #[test]
        fn op_brk() {
            let mut mem: [u8; 65535] = [0; 65535];
            let mut cpu = CPU::new();
            cpu.reset(&mem);
            // set some PC address and a carry bit
            cpu.r.PC.set(0x1234);
            cpu.r.P.C = true;

            cpu.op_brk(Opcode::BRK, &mut mem);
            assert_eq!(
                cpu.r.P,
                StatusRegister {
                    B: true,
                    I: true,
                    C: true,
                    ..Default::default()
                }
            );
            assert_eq!(u16::from(cpu.r.PC), ADDR_IRQ_VECTOR);
            assert_eq!(cpu.wait, 7);
            assert_eq!(
                StatusRegister::from(cpu.pop(&mem)),
                StatusRegister {
                    C: true,
                    ..Default::default()
                }
            );
            assert_eq!(cpu.pop_addr(&mem), 0x1234 + 1);
        }
    }
}
