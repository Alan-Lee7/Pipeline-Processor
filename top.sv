module testbench();

  logic        clk;
  logic        reset;

  logic [31:0] WriteDataM, DataAdrM;
  logic        MemWriteM;

  // instantiate device to be tested
  top dut(clk, reset, WriteDataM, DataAdrM, MemWriteM);
  
  // initialize test
  initial
    begin-
      reset <= 1; # 22; reset <= 0;
    end

  // generate clock to sequence tests
  always
    begin
      clk <= 1; # 5; clk <= 0; # 5;
    end

  // check results
  always @(negedge clk)
    begin
      if(MemWriteM) begin
        if(DataAdrM === 104 & WriteDataM === 25) begin
          $display("Simulation succeeded");
          $stop;
        end else if (DataAdrM !== 96) begin
          $display("Simulation failed");
          $stop;
        end
      end
    end
endmodule
///////////////////////////////////////////////////////////
///// End Testbench                                   /////
///////////////////////////////////////////////////////////


module top(input logic clk, reset,
	output logic [31:0] WriteDataM, DataAdrM,
	output logic MemWriteM);
	logic [31:0] PCF, InstrF, ReadDataM;

	// instantiate processor and memories
	riscv riscv(clk, reset, PCF, InstrF, MemWriteM, DataAdrM,
	WriteDataM, ReadDataM);
	imem imem(PCF, InstrF);
	dmem dmem(clk, MemWriteM, DataAdrM, WriteDataM, ReadDataM);
endmodule


module riscv(input logic        clk, reset,
                   output logic [31:0] PCF,
                   input  logic [31:0] InstrF,
                   output logic        MemWriteM,
                   output logic [31:0] DataAdrM, WriteDataM,
                   input  logic [31:0] ReadDataM);

  logic       ALUSrcE, RegWriteM, RegWriteW, ZeroE, NegativeE, PCSrcE;
  logic		  StallF, StallD, FlushD, FlushE;
  logic [1:0] ResultSrcE, ResultSrcW, ForwardAE, ForwardBE;
  logic [2:0] ImmSrcD;
  logic [3:0] ALUControlE;
  logic [4:0] Rs1E, Rs2E, RdE, RdM, RdW;
  logic [31:0] InstrD;
  
  //Good
  datapath dp(clk, reset, ResultSrcW, PCSrcE,
              ALUSrcE, RegWriteW,
              ImmSrcD, ALUControlE,
              ZeroE, NegativeE, PCF, InstrF, InstrD,
              DataAdrM, WriteDataM, ReadDataM,
				  StallF, StallD, FlushD, FlushE, ForwardAE, ForwardBE,
				  Rs1E, Rs2E, RdE, RdM, RdW);
				  
  controller c(clk, reset, InstrD[6:0], InstrD[14:12], InstrD[30], ZeroE,
              NegativeE, FlushE, ResultSrcE, ResultSrcW, MemWriteM, PCSrcE,
              ALUSrcE, RegWriteM, RegWriteW,
              ImmSrcD, ALUControlE);
				  
  hazardunit hu(InstrD[19:15], InstrD[24:20], Rs1E, Rs2E, RdE,
				  PCSrcE, ResultSrcE[0], RdM, RegWriteM, RdW,
				  RegWriteW, StallF, StallD, FlushD, FlushE,
				  ForwardAE, ForwardBE);

				  
endmodule

module controller(input  logic clk, reset,
						input  logic [6:0] op,
                  input  logic [2:0] funct3,
                  input  logic       funct7b5,
                  input  logic       ZeroE,
						input	 logic		 NegativeE,
						input  logic		 FlushE,
						output logic [1:0] ResultSrcE,
                  output logic [1:0] ResultSrcW,
                  output logic       MemWriteM,
                  output logic       PCSrcE, ALUSrcE,
                  output logic       RegWriteM,
						output logic		 RegWriteW,
                  output logic [2:0] ImmSrcD,
                  output logic [3:0] ALUControlE);

  logic [1:0] ALUOp;
  logic beq, blt;
  
  //Initial Output
  logic RegWriteD, MemWriteD, JumpD, BranchD, ALUSrcD;
  logic [1:0] ResultSrcD;
  logic [3:0] ALUControlD;
  logic [4:0] Rs1D, Rs2D;
  
  //First Flopr
  logic RegWriteE, MemWriteE, JumpE, BranchE;
  
  //Second Flopr
  logic [1:0] ResultSrcM;
  
  //Get outputs
  maindec md(op, ResultSrcD, MemWriteD, BranchD,
					ALUSrcD, RegWriteD, JumpD, ImmSrcD, ALUOp);
  aludec  ad(op[5], funct3, funct7b5, ALUOp, ALUControlD);
  
  //First Flopr
  flopr_clear #(1) writeE(clk, reset, FlushE, RegWriteD, RegWriteE);
  flopr_clear #(2) resultE(clk, reset, FlushE, ResultSrcD, ResultSrcE);
  flopr_clear #(1) memE(clk, reset, FlushE, MemWriteD, MemWriteE);
  flopr_clear #(1) jumpE(clk, reset, FlushE, JumpD, JumpE);
  flopr_clear #(1) branchE(clk, reset, FlushE, BranchD, BranchE);
  flopr_clear #(4) actrlE(clk, reset, FlushE, ALUControlD, ALUControlE);
  flopr_clear #(1) asrcE(clk, reset, FlushE, ALUSrcD, ALUSrcE);
  
  //Second Flopr
  flopr #(1) writeM(clk, reset, RegWriteE, RegWriteM);
  flopr #(2) resultM(clk, reset, ResultSrcE, ResultSrcM);
  flopr #(1) memM(clk, reset, MemWriteE, MemWriteM);
	 
  //Third Flopr
  flopr #(1) writeW(clk, reset, RegWriteM, RegWriteW);
  flopr #(2) resultW(clk, reset, ResultSrcM, ResultSrcW);
  
  assign beq = ZeroE && (funct3 == 3'b000);
  assign blt = NegativeE && (funct3 == 3'b000);
  assign PCSrcE = (BranchE && (beq || blt)) || JumpE;
						
endmodule

module maindec(input  logic [6:0] op,
               output logic [1:0] ResultSrcD,
               output logic       MemWriteD,
               output logic       BranchD, ALUSrcD,
               output logic       RegWriteD, JumpD,
               output logic [2:0] ImmSrcD,
               output logic [1:0] ALUOp);

  logic [11:0] controls;

  assign {RegWriteD, ImmSrcD, ALUSrcD, MemWriteD,
          ResultSrcD, BranchD, ALUOp, JumpD} = controls;

  always_comb
    case(op)
    // RegWrite_ImmSrc_ALUSrc_MemWrite_ResultSrc_Branch_ALUOp_Jump
      7'b0000011: controls = 12'b1_000_1_0_01_0_00_0; // lw	
		7'b0100011: controls = 12'b0_001_1_1_00_0_00_0; // sw
      7'b0110011: controls = 12'b1_000_0_0_00_0_10_0; // R-type
      7'b1100011: controls = 12'b0_010_0_0_00_1_01_0; // beq
      7'b0010011: controls = 12'b1_000_1_0_00_0_10_0; // I-type ALU
      7'b1101111: controls = 12'b1_011_0_0_10_0_00_1; // jal
		7'b0110111: controls = 12'b1_100_0_0_00_0_10_0; // lui
      default:    controls = 12'b0_000_0_0_00_0_00_0; // non-implemented instruction
    endcase
endmodule

module aludec(input  logic       opb5,
              input  logic [2:0] funct3,
              input  logic       funct7b5, 
              input  logic [1:0] ALUOp,
              output logic [3:0] ALUControl);

  logic  RtypeSub;
  assign RtypeSub = funct7b5 & opb5;  // TRUE for R-type subtract instruction

  always_comb
    case(ALUOp)
      2'b00:                ALUControl = 4'b0000; // addition
      2'b01:                ALUControl = 4'b0001; // subtraction
      default: case(funct3) // R-type or I-type ALU
                 3'b000:  if (RtypeSub) 
                            ALUControl = 4'b0001; // sub
                          else          
                            ALUControl = 4'b0000; // add, addi
					  3'b010:    ALUControl = 4'b0101; // slt, slti
					  3'b001: 	 ALUControl = 4'b1000; // sra
                 3'b110:    ALUControl = 4'b0011; // or, ori
                 3'b111:    ALUControl = 4'b0010; // and, andi
                 default:   ALUControl = 4'b0000; // ???
               endcase
    endcase
endmodule

module datapath(input  logic        clk, reset,
                input  logic [1:0]  ResultSrcW,						
                input  logic        PCSrcE, ALUSrcE,
                input  logic        RegWriteW,
                input  logic [2:0]  ImmSrcD,
                input  logic [3:0]  ALUControlE,
                output logic        ZeroE,
					 output logic			NegativeE,
                output logic [31:0] PCF,
                input  logic [31:0] InstrF,
					 output logic [31:0] InstrD,
                output logic [31:0] DataAdrM, WriteDataM,
                input  logic [31:0] ReadDataM,
					 input  logic StallF,
					 input  logic StallD,
					 input  logic FlushD,
					 input  logic FlushE,
					 input  logic [1:0] ForwardAE,
					 input  logic [1:0] ForwardBE,
					 output logic [4:0] Rs1E,
					 output logic [4:0] Rs2E,
					 output logic [4:0] RdE,
					 output logic [4:0] RdM,
					 output logic [4:0] RdW);

				  
  logic [31:0] PCF_Prime, PCD, PCE, PCPlus4F, PCPlus4D, PCPlus4E, PCPlus4M, PCPlus4W, PCTargetE;
  logic [31:0] ImmExtD, ImmExtE, ReadDataW, ALUResultE, RD1, RD2, RD1E, RD2E, ALUResultW;
  logic [31:0] SrcAE, SrcBE;
  logic [31:0] ResultW, WriteDataE;
  logic [4:0]  RdD;

  //Left of En_CLR_FLPR x
  mux2 #(32) 					PCFPrime(PCPlus4F, PCTargetE, PCSrcE, PCF_Prime);
  flopr_enable #(32) 		PCFPrimetoPCF(clk, reset, ~StallF, PCF_Prime, PCF);
  adder							PCFadd4(PCF, 32'd4, PCPlus4F);
  
  flopr_enable_clear #(32) PCFFlopr(clk, reset, ~StallD, FlushD, PCF, PCD);
  flopr_enable_clear #(32) InstrFFlopr(clk, reset, ~StallD, FlushD, InstrF, InstrD);
  flopr_enable_clear #(32) PCPlusFlopr(clk, reset, ~StallD, FlushD, PCPlus4F, PCPlus4D);
  
  //Right of EN_CLR_FLPR & Left of CLR_FLPR
  regfile     rf(~clk, RegWriteW, InstrD[19:15], InstrD[24:20], 
              RdW, ResultW, RD1, RD2);
  extend      ext(InstrD[31:7], ImmSrcD, ImmExtD);

  flopr_clear #(32) RD1Flopr(clk, reset, FlushE, RD1, RD1E);
  flopr_clear #(32) RD2Flopr(clk, reset, FlushE, RD2, RD2E);
  flopr_clear #(32) PCDFlopr(clk, reset, FlushE, PCD, PCE);
  
  flopr_clear #(5) RS1DFlopr(clk, reset, FlushE, InstrD[19:15], Rs1E);
  flopr_clear #(5) Rs2DFlopr(clk, reset, FlushE, InstrD[24:20], Rs2E);
  flopr_clear #(5) RdDFlopr(clk, reset, FlushE, InstrD[11:7], RdE);
  flopr_clear #(32) ImmExtFlopr(clk, reset, FlushE, ImmExtD, ImmExtE);
  flopr_clear #(32) PCPlus4DFlopr(clk, reset, FlushE, PCPlus4D, PCPlus4E);
  
  //Right of CLR_FLPR & Left of First FLPR
  mux3 #(32)  SrcAEmux(RD1E, ResultW, DataAdrM, ForwardAE, SrcAE);
  mux3 #(32)  WriteDataEmux(RD2E, ResultW, DataAdrM, ForwardBE, WriteDataE);
  mux2 #(32)  SrcBEmux(WriteDataE, ImmExtE, ALUSrcE, SrcBE);
  alu         alu(SrcAE, SrcBE, ALUControlE, ALUResultE, ZeroE, NegativeE);
  
  flopr #(32) ALUResultEFlopr(clk, reset, ALUResultE, DataAdrM);
  flopr #(32) WriteDataEFlopr(clk, reset, WriteDataE, WriteDataM);
  adder		  PCEImmExtEAddr(PCE, ImmExtE, PCTargetE);
  flopr #(5) RdEFlopr(clk, reset, RdE, RdM);
  flopr #(32) PCPlus4EFlopr(clk, reset, PCPlus4E, PCPlus4M);
  
  //Between last two FLPRs
  flopr #(32) ALUResultMFlopr(clk, reset, DataAdrM, ALUResultW);
  flopr #(32) ReadDataMFlopr(clk, reset, ReadDataM, ReadDataW);
  flopr #(5) RdMFlopr(clk, reset, RdM, RdW);
  flopr #(32) PCPlus4MFlopr(clk, reset, PCPlus4M, PCPlus4W);
  
  //Right of last FLPR
  mux3 #(32) ResultWmux(ALUResultW, ReadDataW, PCPlus4W, ResultSrcW, ResultW);

endmodule

module hazardunit(input logic [4:0] Rs1D,
						input logic [4:0] Rs2D,
						input logic [4:0] Rs1E,
						input logic [4:0] Rs2E,
						input logic [4:0] RdE,
						input logic PCSrcE,
						input logic ResultSrcE,
						input logic [4:0] RdM,
						input logic RegWriteM,
						input logic [4:0] RdW,
						input logic RegWriteW,
						output logic StallF,
						output logic StallD,
						output logic FlushD,
						output logic FlushE,
						output logic [1:0] ForwardAE,
						output logic [1:0] ForwardBE);

	logic lwStall;
	
	//Rs1E
always_comb begin
	if (((Rs1E == RdM) && RegWriteM) && (Rs1E != 0)) 
			  ForwardAE = 2'b10;
		 else if (((Rs1E == RdW) && RegWriteW) && (Rs1E != 0)) 
			  ForwardAE = 2'b01;
		 else 
			  ForwardAE = 2'b00;

	//Rs2E
		 if (((Rs2E == RdM) && RegWriteM) && (Rs2E != 0)) 
			  ForwardBE = 2'b10;
		 else if (((Rs2E == RdW) && RegWriteW) && (Rs2E != 0)) 
			  ForwardBE = 2'b01;
		 else 
			  ForwardBE = 2'b00;
end

	
	assign lwStall = ((Rs1D == RdE) || (Rs2D == RdE)) && ResultSrcE;
	assign StallF = lwStall;
	assign StallD = lwStall;
	
	assign FlushD = PCSrcE;
	assign FlushE = lwStall || PCSrcE;

endmodule

module regfile(input  logic        clk, 
               input  logic        we3, 
               input  logic [ 4:0] a1, a2, a3, 
               input  logic [31:0] wd3, 
               output logic [31:0] rd1, rd2);

  logic [31:0] rf[31:0];

  // three ported register file
  // read two ports combinationally (A1/RD1, A2/RD2)
  // write third port on rising edge of clock (A3/WD3/WE3)
  // register 0 hardwired to 0

  always_ff @(posedge clk)
    if (we3) rf[a3] <= wd3;	

  assign rd1 = (a1 != 0) ? rf[a1] : 0;
  assign rd2 = (a2 != 0) ? rf[a2] : 0;
endmodule

module adder(input  [31:0] a, b,
             output [31:0] y);
	
  assign y = a + b;
endmodule

module extend(input  logic [31:7] instr,
              input  logic [2:0]  immsrc,
              output logic [31:0] immext);
 
  always_comb
    case(immsrc) 
               // I-type 
      3'b000:   immext = {{20{instr[31]}}, instr[31:20]};  
               // S-type (stores)
      3'b001:   immext = {{20{instr[31]}}, instr[31:25], instr[11:7]};
               // B-type (branches)
      3'b010:   immext = {{20{instr[31]}}, instr[7], instr[30:25], instr[11:8], 1'b0};
               // J-type (jal)
      3'b011:   immext = {{12{instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0};
					// U-type
      3'b100: 	 immext = {instr[31:12], 12'b0};
					// undefined
      default: immext = 32'b0;
    endcase             
endmodule

module flopr #(parameter WIDTH = 8)
              (input  logic             clk, reset,
               input  logic [WIDTH-1:0] d, 
               output logic [WIDTH-1:0] q);

  always_ff @(posedge clk, posedge reset)
    if (reset) q <= 0;
    else       q <= d;
endmodule

module flopr_clear #(parameter WIDTH = 8)
              (input  logic             clk, reset,
					input  logic clear,
               input  logic [WIDTH-1:0] d, 
               output logic [WIDTH-1:0] q);

  always_ff @(posedge clk, posedge reset)
    if (reset) q <= 0;
    else if(clear) q <= 0;
	 else q <= d;
endmodule

module flopr_enable #(parameter WIDTH = 8)
              (input  logic clk, reset,
				   input  logic enable,
               input  logic [WIDTH-1:0] d, 
               output logic [WIDTH-1:0] q);

  always_ff @(posedge clk, posedge reset)
    if (reset) q <= 0;
    else if(enable) q <= d;
endmodule

module flopr_enable_clear #(parameter WIDTH = 8)
              (input  logic clk, reset,
				   input  logic enable,
					input  logic clear,
               input  logic [WIDTH-1:0] d, 
               output logic [WIDTH-1:0] q);

  always_ff @(posedge clk, posedge reset)
    if (reset) q <= 0;
	 else if(clear) q <= 0;
    else if(enable) q <= d;
endmodule

module mux2 #(parameter WIDTH = 8)
             (input  logic [WIDTH-1:0] d0, d1, 
              input  logic             s, 
              output logic [WIDTH-1:0] y);

  assign y = s ? d1 : d0; 
endmodule

module mux3 #(parameter WIDTH = 8)
             (input  logic [WIDTH-1:0] d0, d1, d2,
              input  logic [1:0]       s, 
              output logic [WIDTH-1:0] y);

  assign y = s[1] ? d2 : (s[0] ? d1 : d0); 
endmodule

module imem(input  logic [31:0] a,
            output logic [31:0] rd);

  logic [31:0] RAM[63:0];

  initial
      $readmemh("riscvtest.txt",RAM);

  assign rd = RAM[a[31:2]]; // word aligned
endmodule

module dmem(input  logic        clk, we,
            input  logic [31:0] a, wd,
            output logic [31:0] rd);

  logic [31:0] RAM[63:0];

  assign rd = RAM[a[31:2]]; // word aligned

  always_ff @(posedge clk)
    if (we) RAM[a[31:2]] <= wd;
endmodule

module alu(input  logic [31:0] a, b,
           input  logic [3:0]  alucontrol,
           output logic [31:0] result,
           output logic        zero,
			  output logic 		 negative);

  logic [31:0] condinvb, sum;
  logic        v;              // overflow
  logic        isAddSub;       // true when is add or subtract operation

  assign condinvb = alucontrol[0] ? ~b : b;
  assign sum = a + condinvb + alucontrol[0];
  assign isAddSub = ~alucontrol[2] & ~alucontrol[1] |
                    ~alucontrol[1] & alucontrol[0];

  always_comb
    case (alucontrol)
      4'b0000:  result = sum;                // add
      4'b0001:  result = sum;                // subtract
      4'b0010:  result = a & b;              // and
      4'b0011:  result = a | b;       			// or
      4'b0100:  result = a ^ b;       			// xor
      4'b0101:  result = (a < b) ? 1:0;		// slt
      4'b0110:  result = a << b;         		// sll
      4'b0111:  result = a >> b;        		// srl
		4'b1000:  result = a >>> b[4:0];			// sra
      default:  result = 32'b0;
    endcase

  assign zero = (result == 32'b0);
  assign negative = (result[31] == 1);
  assign v = ~(alucontrol[0] ^ a[31] ^ b[31]) & (a[31] ^ sum[31]) & isAddSub;
  
endmodule
