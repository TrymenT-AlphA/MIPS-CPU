`timescale 1ns / 1ps

module CPU(
    input logic clk,
    input logic rst,
    output logic [6:0] seg7,
    output logic [3:0] an
);
    logic clk200Hz;
    fenpin #250000 fp2(.clk(clk), .rst(rst), .clk_out(clk200Hz));
    logic [5:0] OpD, FunctD;
    logic FlushE;
    logic [31:0] RD1D, RD2D;
    logic JumpD, PCSrcD;
    logic RegWriteD, RegWriteE, RegWriteM, RegWriteW;
    logic MemtoRegD, MemtoRegE, MemtoRegM, MemtoRegW;
    logic MemWriteD, MemWriteE, MemWriteM;
    logic [2:0] ALUControlD, ALUControlE;
    logic ALUSrcD, ALUSrcE;
    logic RegDstD, RegDstE;
    logic BranchD;

    ControlUnit cu(
        .clk(clk),
        .rst(rst),
        .OpD(OpD),
        .FunctD(FunctD),
        .FlushE(FlushE),
        .RD1D(RD1D), 
        .RD2D(RD2D),
        
        .JumpD(JumpD),
        .PCSrcD(PCSrcD),
        
        .RegWriteD(RegWriteD),
        .RegWriteE(RegWriteE),
        .RegWriteM(RegWriteM),
        .RegWriteW(RegWriteW),

        .MemtoRegD(MemtoRegD),
        .MemtoRegE(MemtoRegE),
        .MemtoRegM(MemtoRegM),
        .MemtoRegW(MemtoRegW),
        
        .MemWriteD(MemWriteD),
        .MemWriteE(MemWriteE),
        .MemWriteM(MemWriteM),
        
        .ALUControlD(ALUControlD),
        .ALUControlE(ALUControlE),

        .ALUSrcD(ALUSrcD),
        .ALUSrcE(ALUSrcE),

        .RegDstD(RegDstD),
        .RegDstE(RegDstE),

        .BranchD(BranchD)
    );

    logic [4:0] RsD, RsE, RtD, RtE;
    logic [4:0] WriteRegE, WriteRegM, WriteRegW; 
    logic ForwardAD, ForwardBD;
    logic [1:0] ForwardAE, ForwardBE;
    logic StallD, StallF;

    ConflictUnit cfu(
        .RsD(RsD),
        .RsE(RsE),
        .RtD(RtD),
        .RtE(RtE),
        .RegWriteE(RegWriteE),
        .RegWriteM(RegWriteM),
        .RegWriteW(RegWriteW),
        .WriteRegE(WriteRegE),
        .WriteRegM(WriteRegM),
        .WriteRegW(WriteRegW),
        .BranchD(BranchD),
        .MemtoRegE(MemtoRegE),
        .MemtoRegM(MemtoRegM),
        .ForwardAD(ForwardAD),
        .ForwardBD(ForwardBD),
        .ForwardAE(ForwardAE),
        .ForwardBE(ForwardBE),
        .StallD(StallD),
        .StallF(StallF),
        .FlushE(FlushE)
    );

    logic [31:0] t_PCF, _PCF, PCF, PCPlus4F, PCPlus4D, PCBranchD, InstrD, InstrF;

    PC #(32) pcreg(
        .clk(clk),
        .rst(rst),
        .en(~StallD),
        ._D(_PCF),
        .D(PCF)
    );

    IR ir(
        .rst(rst),
        .RA(PCF),
        .RD(InstrF)
    );

    Adder pcadd1(
        .A(PCF), 
        .B(32'b100),
        .Y(PCPlus4F)
    );

    Mux2 #(32) pcbrmux(
        .D0(PCPlus4F), 
        .D1(PCBranchD), 
        .S(PCSrcD), 
        .Y(t_PCF)
    );
    Mux2 #(32) pcmux(
        .D0(t_PCF), 
        .D1({PCPlus4D[31:28],InstrD[25:0],2'b00}),
        .S(JumpD),
        .Y(_PCF)
    );

    logic [31:0] ResultW, RD1, RD2,result;

    RF rf(
        .clk(~clk),
        .rst(rst),
        .RA1(RsD),
        .RA2(RtD),
        .WA3(WriteRegW),
        .WD3(ResultW),
        .WE3(RegWriteW),
        .RD1(RD1),
        .RD2(RD2),
        .result(result)
    );

    logic [31:0] SignImmD, SignImmshD, SignImmE;

    SignExt se(.A(InstrD[15:0]), .Y(SignImmD));
    SL2 immsh(.A(SignImmD), .Y(SignImmshD));
    Adder pcadd2(.A(PCPlus4D), .B(SignImmshD), .Y(PCBranchD));
    
    logic [31:0] ALUOutM;

    Mux2 #(32) forwardamux(
        .D0(RD1),
        .D1(ALUOutM),
        .S(ForwardAD),
        .Y(RD1D)
    );
    Mux2 #(32) forwardbmux(
        .D0(RD2),
        .D1(ALUOutM),
        .S(ForwardBD),
        .Y(RD2D)
    );

    Flopenr #(32) r1D(
        .clk(clk),
        .rst(rst),
        .en(~StallD),
        ._D(PCPlus4F),
        .D(PCPlus4D)
    );
    
    logic FlushD;
    
    assign FlushD = PCSrcD | JumpD;
    
    Flopenrc #(32) r2D(
        .clk(clk),
        .rst(rst),
        .en(~StallD),
        .clr(FlushD),
        ._D(InstrF),
        .D(InstrD)
    );

    logic [4:0] RdD, RdE;

	assign OpD = InstrD[31:26];
	assign FunctD = InstrD[5:0];
	assign RsD = InstrD[25:21];
	assign RtD = InstrD[20:16];
	assign RdD = InstrD[15:11];

    logic [31:0] RD1E, RD2E;

    Floprc #(32) r1E(
        .clk(clk),
        .rst(rst),
        .clr(FlushE),
        ._D(RD1),
        .D(RD1E)
    );
    Floprc #(32) r2E(
        .clk(clk),
        .rst(rst),
        .clr(FlushE),
        ._D(RD2),
        .D(RD2E)
    );
    Floprc #(32) r3E(
        .clk(clk),
        .rst(rst),
        .clr(FlushE),
        ._D(SignImmD),
        .D(SignImmE)
    );
    Floprc #(5) r4E(
        .clk(clk),
        .rst(rst),
        .clr(FlushE),
        ._D(RsD),
        .D(RsE)
    );
    Floprc #(5) r5E(
        .clk(clk),
        .rst(rst),
        .clr(FlushE),
        ._D(RtD),
        .D(RtE)
    );
    Floprc #(5) r6E(
        .clk(clk),
        .rst(rst),
        .clr(FlushE),
        ._D(RdD),
        .D(RdE)
    );

    logic [31:0] SrcAE, SrcBE, tSrcBE;

    Mux3 #(32) forwardaemux(
        .D0(RD1E),
        .D1(ResultW),
        .D2(ALUOutM),
        .S(ForwardAE),
        .Y(SrcAE)
    );
    Mux3 #(32) forwardbemux(
        .D0(RD2E),
        .D1(ResultW),
        .D2(ALUOutM),
        .S(ForwardBE),
        .Y(tSrcBE)
    );
    Mux2 #(32) srcbmux(
        .D0(tSrcBE),
        .D1(SignImmE),
        .S(ALUSrcE),
        .Y(SrcBE)
    );

    logic [31:0] ALUOutE, ALUOutW;

    ALU alu(
        .A(SrcAE),
        .B(SrcBE),
        .F(ALUControlE),
        .Y(ALUOutE),
        .Zero(Zero),
        .OverFlow(OverFlow)

    );

    Mux2 #(5) wrmux(
        .D0(RtE),
        .D1(RdE),
        .S(RegDstE),
        .Y(WriteRegE)
    );

    logic [31:0] WriteDataM;

    Flopr #(32) r1M(
        .clk(clk),
        .rst(rst),
        ._D(tSrcBE),
        .D(WriteDataM)
    );
    Flopr #(32) r2M(
        .clk(clk),
        .rst(rst),
        ._D(ALUOutE),
        .D(ALUOutM)
    );
    Flopr #(5) r3M(
        .clk(clk),
        .rst(rst),
        ._D(WriteRegE),
        .D(WriteRegM)
    );

    Flopr #(32) r1W(
        .clk(clk),
        .rst(rst),
        ._D(ALUOutM),
        .D(ALUOutW)
    );

    logic [31:0] ReadDataM, ReadDataW;

    DM dm(
        .clk(clk),
        .rst(rst),
        .RA(ALUOutM),
        .WD(WriteDataM),
        .WE(MemWriteM),
        .RD(ReadDataM)
    );

    Flopr #(32) r2W(
        .clk(clk),
        .rst(rst),
        ._D(ReadDataM),
        .D(ReadDataW)
    );
    Flopr #(5) r3W(
        .clk(clk),
        .rst(rst),
        ._D(WriteRegM),
        .D(WriteRegW)
    );
	Mux2 #(32) resmux(
        .D0(ALUOutW),
        .D1(ReadDataW),
        .S(MemtoRegW),
        .Y(ResultW)
    );
    
    display dut2(.clk(clk200Hz), .rst(rst), .data(result), .seg7(seg7), .an(an));
    
endmodule

module Adder(
    input logic [31:0] A,
    input logic [31:0] B,
    output logic [31:0] Y
);

    assign Y = A + B;

endmodule

module ALU(
    input logic [31:0] A,
    input logic [31:0] B,
    input logic [2:0] F,
    output logic [31:0] Y,
    output logic Zero,
    output logic OverFlow
);

    logic [31:0] BB, S;

    assign BB = (F[2]) ? ~B : B;
    assign S = A + BB + F[2];

    always_comb 
        case(F[1:0])
            2'b00: Y = A & BB;
            2'b01: Y = A | BB;
            2'b10: Y = S;
            2'b11: Y = {31'b0,S[31]};
        endcase

    assign Zero = (Y==32'b0);

    always_comb
        case(F[2:1])
            2'b01: OverFlow = A[31] & B[31] & ~S[31] | ~A[31] & ~B[31] & S[31];
            2'b11: OverFlow = ~A[31] & B[31] & S[31] | A[31] & ~B[31] & ~S[31];
            default: OverFlow = 1'b0;
        endcase

endmodule

module ALUDecoder(
    input logic [5:0] FunctD,
    input logic [1:0] ALUOpD,
    output logic [2:0] ALUControlD
);

    always_comb
        case(ALUOpD)
            2'b00: ALUControlD = 3'b010;            // add (for lw/sw/addi)
            2'b01: ALUControlD = 3'b110;            // sub (for beq)
            2'b11: ALUControlD = 3'b000;
            default: case(FunctD)                   // R-type
                6'b100000: ALUControlD = 3'b010;    // add
                6'b100010: ALUControlD = 3'b110;    // sub
                6'b100100: ALUControlD = 3'b000;    // and
                6'b100101: ALUControlD = 3'b001;    // or
                6'b101010: ALUControlD = 3'b111;    // slt
                default:   ALUControlD = 3'b000;    // ???
            endcase
        endcase

endmodule

module ConflictUnit(
    input logic [4:0] RsD,
    input logic [4:0] RsE,
    input logic [4:0] RtD,
    input logic [4:0] RtE,
    input logic RegWriteE,
    input logic RegWriteM,
    input logic RegWriteW,
    input logic [4:0] WriteRegE,
    input logic [4:0] WriteRegM,
    input logic [4:0] WriteRegW,
    input logic BranchD,
    input logic MemtoRegE,
    input logic MemtoRegM,
    output logic ForwardAD,
    output logic ForwardBD,
    output logic [1:0] ForwardAE,
    output logic [1:0] ForwardBE,
    output logic StallF,
    output logic StallD,
    output logic FlushE
);

    logic lwstallD, branchstallD;

    assign ForwardAD = (RsD != 0 & RsD == WriteRegM & RegWriteM);
    assign ForwardBD = (RtD != 0 & RtD == WriteRegM & RegWriteM);

    always_comb begin
        ForwardAE = 2'b00;
        ForwardBE = 2'b00;
        if (RsE != 0) begin
            if (RsE == WriteRegM & RegWriteM) 
                ForwardAE = 2'b10;
            else if (RsE == WriteRegW & RegWriteW)
                ForwardAE = 2'b01;
        end
        if (RtE != 0) begin
            if (RtE == WriteRegM & RegWriteM) 
                ForwardBE = 2'b10;
            else if (RtE == WriteRegW & RegWriteW)
                ForwardBE = 2'b01;
        end
    end

    assign #1 lwstallD = MemtoRegE & (RtE == RsD | RtE == RtD);
    assign #1 branchstallD = BranchD &
                            (RegWriteE & 
                            (WriteRegE == RsD | WriteRegE == RtD) | 
                            MemtoRegM &
                            (WriteRegM == RsD | WriteRegM == RtD));
    assign #1 StallD = lwstallD | branchstallD;
    assign #1 StallF = StallD;
    assign #1 FlushE = StallD;

endmodule

module ControlUnit(
    input logic clk,
    input logic rst,
    input logic [5:0] OpD,
    input logic [5:0] FunctD,
    input logic FlushE,
    input logic [31:0] RD1D, RD2D,
    
    output logic JumpD,
    output logic PCSrcD,
    
    output logic RegWriteD,
    output logic RegWriteE,
    output logic RegWriteM,
    output logic RegWriteW,

    output logic MemtoRegD,
    output logic MemtoRegE,
    output logic MemtoRegM,
    output logic MemtoRegW,
    
    output logic MemWriteD,
    output logic MemWriteE,
    output logic MemWriteM,
    
    output logic [2:0] ALUControlD,
    output logic [2:0] ALUControlE,

    output logic ALUSrcD,
    output logic ALUSrcE,

    output logic RegDstD,
    output logic RegDstE,

    output logic BranchD

);

    // ID
    logic [1:0] ALUOpD;

    MainDecoder md(
        .OpD(OpD),
        .MemtoRegD(MemtoRegD),
        .MemWriteD(MemWriteD),
        .BranchD(BranchD),
        .ALUSrcD(ALUSrcD),
        .RegDstD(RegDstD),
        .RegWriteD(RegWriteD),
        .JumpD(JumpD),
        .ALUOpD(ALUOpD)
    );
    
    ALUDecoder ad(
        .FunctD(FunctD),
        .ALUOpD(ALUOpD),
        .ALUControlD(ALUControlD)
    );

    logic EqualD;
    
    EqCmp cmp(
        .A(RD1D),
        .B(RD2D),
        .Y(EqualD)
    );

    assign PCSrcD = BranchD & EqualD;

    // pipline
    Floprc #(8) regE(
        .clk(clk),
        .rst(rst),
        .clr(FlushE),
        ._D({MemtoRegD,MemWriteD,ALUSrcD,RegDstD,RegWriteD,ALUControlD}),
        .D({MemtoRegE,MemWriteE,ALUSrcE,RegDstE,RegWriteE,ALUControlE})
    );
    
    Flopr #(3) regM(
        .clk(clk),
        .rst(rst),
        ._D({MemtoRegE,MemWriteE,RegWriteE}),
        .D({MemtoRegM,MemWriteM,RegWriteM})
    );
    Flopr #(2) regW(
        .clk(clk),
        .rst(rst),
        ._D({MemtoRegM,RegWriteM}),
        .D({MemtoRegW,RegWriteW})
    );
endmodule 

module DM(
    input logic clk,
    input logic rst,
    input logic [31:0] RA,
    input logic [31:0] WD,
    input logic WE,
    output logic [31:0] RD
);

    logic [31:0] memory [5:0];

    always_ff @(negedge clk, posedge rst)
        if (rst) for (integer i = 0; i <= 5; i=i+1)
            memory[i] = 32'b0;
        else if (WE) memory[RA] <= WD;

    assign RD = memory[RA];

endmodule

module EqCmp(
    input logic [31:0] A,
    input logic [31:0] B,
    output logic Y
);

    assign Y = (A == B) ? 1'b1 : 1'b0;

endmodule

module Flopenr #(parameter WIDTH = 8)(
    input logic clk,
    input logic rst,
    input logic en,
    input logic [WIDTH-1:0] _D,
    output logic [WIDTH-1:0] D
);

    always_ff @(posedge clk, posedge rst)
        if (rst) D <= 0;
        else if (en) D <= _D;

endmodule

module Flopenrc #(parameter WIDTH = 8)(
    input logic clk,
    input logic rst,
    input logic en,
    input logic clr,
    input logic [WIDTH-1:0] _D,
    output logic [WIDTH-1:0] D
);

    always_ff @(posedge clk, posedge rst)
        if (rst) D <= 0;
        else if (clr) D <= 0;
        else if (en) D <= _D;

endmodule

module Flopr #(parameter WIDTH = 8)(
    input logic clk,
    input logic rst,
    input logic [WIDTH-1:0] _D,
    output logic [WIDTH-1:0] D
);

    always_ff @(posedge clk, posedge rst)
        if (rst) D <= 0;
        else D <= _D;

endmodule

module Floprc #(parameter WIDTH = 8)(
    input logic clk,
    input logic rst,
    input logic clr,
    input logic [WIDTH-1:0] _D,
    output logic [WIDTH-1:0] D
);

    always_ff @(posedge clk, posedge rst)
        if (rst) D <= 0;
        else if (clr) D <= 0;
        else D <= _D;

endmodule

module IR(
    input logic rst,
    input logic [31:0] RA,
    output logic [31:0] RD
);

    logic [31:0] memory [7:0];

    assign RD = memory[RA>>2];
    always_ff @(posedge rst)
    begin
        memory[0] <= 32'b00000000000000000001000000100000;
        memory[1] <= 32'b00100000000000010000000000000000;
        memory[2] <= 32'b00100000000000110000000001100101;
        memory[3] <= 32'b00010000001000110000000000000011;
        memory[4] <= 32'b00000000010000010001000000100000;
        memory[5] <= 32'b00100000001000010000000000000001;
        memory[6] <= 32'b00001000000000000000000000000011;
//        memory[7] <= 32'b00000000000000000000000000000000;
        memory[7] <= 32'b00001000000000000000000000000111;
    end

endmodule

module MainDecoder(
    input logic [5:0] OpD,
    
    output logic MemtoRegD, 
    output logic MemWriteD,
    output logic BranchD,
    output logic ALUSrcD,
    output logic RegDstD,
    output logic RegWriteD,
    output logic JumpD,
    output logic [1:0] ALUOpD
);

    logic[8:0] Controls;

    assign {RegWriteD, RegDstD, ALUSrcD, BranchD, MemWriteD, MemtoRegD, JumpD, ALUOpD} = Controls;

    always_comb
        case(OpD)
            6'b000000: Controls = 9'b110000010; // r-type
            6'b100011: Controls = 9'b101001000; // lw
            6'b101011: Controls = 9'b001010000; // sw
            6'b000100: Controls = 9'b000100001; // beq
            6'b001100: Controls = 9'b000100011; // andi
            6'b001000: Controls = 9'b101000000; // addi
            6'b000010: Controls = 9'b000000100; // jump
            default:   Controls = 9'b000000000; // illegal
        endcase

endmodule

module Mux2 #(parameter WIDTH = 8)(
    input logic[WIDTH-1:0] D0,
    input logic[WIDTH-1:0] D1,
    input logic S,
    output logic[WIDTH-1:0] Y
);

    assign Y = (S) ? D1 : D0;

endmodule

module Mux3 #(parameter WIDTH = 8)(
    input logic [WIDTH-1:0] D0,
    input logic [WIDTH-1:0] D1,
    input logic [WIDTH-1:0] D2,
    input logic [1:0] S,
    output logic [WIDTH-1:0] Y
);

    assign Y = (S == 2'b00) ? D0 : 
               (S == 2'b01) ? D1 : 
               (S == 2'b10) ? D2 : D0;

endmodule

module PC #(parameter WIDTH = 8)(
    input logic clk,
    input logic rst,
    input logic en,
    input logic [WIDTH-1:0] _D,
    output logic [WIDTH-1:0] D
);

    always_ff @(posedge clk, posedge rst)
        if (rst) D <= 0;
        else if (en) D <= _D;

endmodule

module RF(
    input clk,
    input rst,
    input logic [4:0] RA1,
    input logic [4:0] RA2,
    input logic [4:0] WA3,
    input logic [31:0] WD3,
    input logic WE3,
    output logic [31:0] RD1,
    output logic [31:0] RD2,
    output logic [31:0] result
);

    logic [31:0] register [3:0];

    always_ff @(posedge clk, posedge rst)
        if (rst) for (integer i = 0; i <= 3; i=i+1)
            register[i] <= 32'b0;
        else if (WE3) 
            register[WA3] <= WD3;

    assign RD1 = (RA1 == 0) ? 0 : register[RA1];
    assign RD2 = (RA2 == 0) ? 0 : register[RA2];
    assign result = register[2];
endmodule

module SignExt(
    input logic [15:0] A,
    output logic [31:0] Y
);

    assign Y = {{16{A[15]}}, A};

endmodule

module SL2(
    input logic [31:0] A,
    output logic [31:0] Y
);

    assign Y = {A[29:0], 2'b00};

endmodule

module display(
    input logic clk,
    input logic rst,
    input logic [31:0] data,
    output logic [6:0] seg7,
    output logic [3:0] an
);

    logic [3:0] number0, number1, number2, number3;
    assign number0 = data % 10;
    assign number1 = data / 10 % 10;
    assign number2 = data / 100 % 10;
    assign number3 = data / 1000;
    
    logic [1:0] op;
    logic [3:0] sel;
    
    always_ff @(posedge clk, posedge rst)
        if (rst) begin
            op <= 2'b00;
        end
        else begin
            case(op)
                2'b00: {sel, an} <= {number3, 4'b0111};
                2'b01: {sel, an} <= {number2, 4'b1011};
                2'b10: {sel, an} <= {number1, 4'b1101};
                2'b11: {sel, an} <= {number0, 4'b1110};
            endcase
            op <= op+2'b01;
        end
        
always_comb
    case(sel)
        4'b0000: seg7 = 7'b1000000;
        4'b0001: seg7 = 7'b1111001;
        4'b0010: seg7 = 7'b0100100;
        4'b0011: seg7 = 7'b0110000;
        4'b0100: seg7 = 7'b0011001;
        4'b0101: seg7 = 7'b0010010;
        4'b0110: seg7 = 7'b0000010;
        4'b0111: seg7 = 7'b1111000;
        4'b1000: seg7 = 7'b0000000;
        4'b1001: seg7 = 7'b0010000;
        default: seg7 = 7'b1000000;
    endcase

endmodule

module fenpin #(parameter tar=50000000)(
    input logic clk, // 100MHz
    input logic rst,
    output logic clk_out
);

    logic [31:0] cnt;

    always_ff @(posedge clk, posedge rst)
        if (rst)
            {clk_out, cnt} <= {1'b0, 32'd0000_0000};
        else if (cnt == tar)
            {clk_out, cnt} <= {~clk_out, 32'd0000_0000};
        else
            cnt <= cnt+1'b1;
endmodule