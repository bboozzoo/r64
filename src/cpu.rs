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
    // CPU6510 is a model of MOS 6510 Microprocessor.
    // Based on http://archive.6502.org/datasheets/mos_6510_mpu.pdf

    struct ProgramCounter {
        PCH: u8,
        PCL: u8,
    }

    struct StatusRegister {
        N: bool, // Negative
        O: bool, // Overflow
        B: bool, // BRK command
        D: bool, // Decimal model
        I: bool, // IRQ disable
        Z: bool, // Zero
        C: bool, // Carry
    }

    struct Registers {
        A: u8,              // Accumulator
        Y: u8,              // Y index register
        X: u8,              // X index register
        PC: ProgramCounter, // (PCH|PCL) program counter
        S: u16,             // Stack pointer
        P: StatusRegister,  // Processor status register
    }

    struct Model {
        r: Registers,
    }

    use crate::component;

    impl component::Clocked for Model {
        fn tick(&self) {
            // noop
        }
    }

    enum Instruction {
        ADS,                    // Add memory to Accumulator with Carry
        AND,                    // AND memory with Accumulator
        ASL,                    // Shift left one bit (memory or Accumulator)

        BCC,                    // Branch on Carry clear
        BCS,                    // Branch on Carry set
        BEQ,                    // Branch on result Zero
        BIT,                    // Test bits in memory with Accumulator
        BMI,                    // Branch on result Negative
        BNE,                    // Branch on result not Zero
        BPL,                    // Branch on result not plus
        BRK,                    // Force break
        BVC,                    // Branch on Overflow clear
        BVS,                    // Branch on Overflow set

        CLC,                    // Clear carry flag
        CLD,                    // Clear Decimal mode
        CLI,                    // Clear Interrupt disable bit
        CLV,                    // Clear Overflow bit
        CMP,                    // Compare memory and Accumulator
        CPX,                    // Compare memory and index X
        CPY,                    // Compare memory and index Y

        DEC,                    // Decrement memory by one
        DEX,                    // Decrement index X by one
        DEY,                    // Decrement index Y by one

        EOR,                    // (exclusive OR) XOR memory or Accumulator

        INC,                    // Increment memory by one
        INX,                    // Increment index X by one
        INY,                    // Increment index Y by one

        JMP,                    // Jump to new location
        JSR,                    // Jump to new location saving return address

        LDA,                    // Load Accumulator with memory
        LDX,                    // Load index X with memory
        LDY,                    // Load index Y with memory
        LSR,                    // Shift right one bit (memory or Accumulator)

        NOP,                    // noop

        ORA,                    // OR memory with Accumulator

        PHA,                    // Push Accumulator on Stack
        PHP,                    // Push processor status on Stack
        PLA,                    // Pull Accumulator from Stack
        PLP,                    // Pull processor status from Stack

        ROL,                    // Rotate one bit left (memory or Accumulator)
        ROR,                    // Rotate one bit right (memory or Accumulator)
        RTI,                    // Return from interrupt
        RTS,                    // Return from subroutine

        SBC,                    // Subtract memory from Accumulator with Borrow
        SEC,                    // Set Carry flag
        SED,                    // Set Decimal flag
        SEI,                    // Set Interrupt disable flag
        STA,                    // Store Accumulator in memory
        STX,                    // Store index X in memory
        STY,                    // Store index Y in memory

        TAX,                    // Transfer Accumulator to index X
        TAY,                    // Transfer Accumulator to index Y
        TSX,                    // Transfer Stack pointer to index X
        TXA,                    // Transfer index X to Accumulator
        TXS,                    // Transfer index X to Stack register
        TYA,                    // Transfer index Y to Accumulator
    }

    impl Model {
        // TODO
    }
}
