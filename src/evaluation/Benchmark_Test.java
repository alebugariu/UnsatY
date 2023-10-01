/*******************************************************************************
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *   
 * Copyright (c) 2021-2023 ETH Zurich.
 *******************************************************************************/
package evaluation;

import java.io.File;
import java.util.LinkedList;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

import proofanalyser.Proof_Analyser_Framework.Prover;
import util.Setup;
import util.Verbal_Output.Log_Type;

/*
 * This class can be used to test the entire proof analysis on benchmarks given
 * as SMT-LIBv2 input files.
 */

public class Benchmark_Test {

	public static void main(String[] args) {
		File tmpFolder = new File("temp");
		tmpFolder.mkdir(); 
		evaluation_z3();
		// evaluation_vampire();
	}

	private static String base_path = "files";

	private static Log_Type log_type = Log_Type.full;

	private static void set_log_type(Log_Type new_log_type) {
		log_type = new_log_type;
	}

	public static void evaluation_z3() {
		Setup.testing_environment = false;
		set_log_type(Log_Type.none);
		ExecutorService executor = Executors.newSingleThreadExecutor();
		try {
			for (String benchmark : successful_z3_benchmarks) {
				File input_file = new File(base_path + File.separator + benchmark);
				Concurrency_Handler.process_file(executor, input_file, Prover.z3, log_type, null);
			}
		} catch (Exception e) {
			System.out.println("\tPROBLEM: " + e.getMessage());
		}
		executor.shutdown();
	}

	public static void evaluation_vampire() {
		Setup.testing_environment = false;
		set_log_type(Log_Type.none);
		ExecutorService executor = Executors.newSingleThreadExecutor();
		try {
			for (String benchmark : successful_vampire_benchmarks) {
				File input_file = new File(base_path + File.separator + benchmark);
				Concurrency_Handler.process_file(executor, input_file, Prover.vampire, log_type, null);
			}
		} catch (Exception e) {
			System.out.println("\tPROBLEM: " + e.getMessage());
		}
		executor.shutdown();
	}

	private static LinkedList<String> successful_z3_benchmarks = new LinkedList<String>() {
		private static final long serialVersionUID = 6314174901629451536L;

		{
			// Test Set 1.
			add("bachelor_thesis/example_application_of_four_nested_functions.smt2");
			add("bachelor_thesis/example_application_of_three_nested_functions.smt2");
			add("bachelor_thesis/example_application_of_two_nested_functions.smt2");
			add("bachelor_thesis/example_barber.smt2");
			add("bachelor_thesis/example_boogie.smt2");
			add("bachelor_thesis/example_combinations.smt2");
			add("bachelor_thesis/example_de_bruijn_index_0.smt2");
			add("bachelor_thesis/example_de_bruijn_index_1.smt2");
			add("bachelor_thesis/example_de_bruijn_index_2.smt2");
			add("bachelor_thesis/example_de_bruijn_index_3.smt2");
			add("bachelor_thesis/example_de_bruijn_index_4.smt2");
			add("bachelor_thesis/example_difference_of_three_quantified_variables_without_patterns.smt2");
			add("bachelor_thesis/example_difference_of_three_quantified_variables_with_patterns.smt2");
			add("bachelor_thesis/example_difference_of_two_quantified_variables.smt2");
			add("bachelor_thesis/example_extract_quantified_variables.smt2");
			add("bachelor_thesis/example_foo.smt2");
			add("bachelor_thesis/example_infinite_possibilities.smt2");
			add("bachelor_thesis/example_infinite_possibilities_constrained.smt2");
			add("bachelor_thesis/example_just_booleans_with_pattern.smt2");
			add("bachelor_thesis/example_just_integers_with_pattern.smt2");
			add("bachelor_thesis/example_linked_list.smt2");
			add("bachelor_thesis/example_negated_quantifier.smt2");
			add("bachelor_thesis/example_nested_function_applications.smt2");
			add("bachelor_thesis/example_nested_quantifier.smt2");
			add("bachelor_thesis/example_no_quantifiers.smt2");
			add("bachelor_thesis/example_product_of_three_quantified_variables.smt2");
			add("bachelor_thesis/example_product_of_two_quantified_variables.smt2");
			add("bachelor_thesis/example_project_description.smt2");
			add("bachelor_thesis/example_project_proposal.smt2");
			add("bachelor_thesis/example_schroedingers_cat.smt2");
			add("bachelor_thesis/example_sequential_quantifiers_1.smt2");
			add("bachelor_thesis/example_sequential_quantifiers_2.smt2");
			add("bachelor_thesis/example_sequential_quantifiers_3.smt2");
			add("bachelor_thesis/example_sum_of_three_constants.smt2");
			add("bachelor_thesis/example_sum_of_three_quantified_variables.smt2");
			add("bachelor_thesis/example_sum_of_two_constants.smt2");
			add("bachelor_thesis/example_sum_of_two_quantified_variables.smt2");
			add("bachelor_thesis/example_survey.smt2");
			add("bachelor_thesis/example_thesis_overview_without_symmetry.smt2");
			add("bachelor_thesis/example_thesis_overview_with_symmetry.smt2");

			// Test Set 2.
			add("fm_paper/fm_paper_figure02.smt2");
			add("fm_paper/fm_paper_figure05.smt2");
			add("fm_paper/fm_paper_figure06.smt2");
			add("fm_paper/fm_paper_figure07.smt2");
			add("fm_paper/fm_paper_figure08.smt2");
			add("fm_paper/fm_paper_figure09.smt2");
			add("fm_paper/fm_paper_figure11.smt2");
			add("fm_paper/fm_paper_figure13.smt2");
			add("fm_paper/fm_paper_figure14.smt2");
			add("fm_paper/fm_paper_figure15.smt2");
			add("fm_paper/fm_paper_figure16.smt2");
			add("fm_paper/fm_paper_figure17.smt2");
			add("fm_paper/fm_paper_figure19.smt2");
			add("fm_paper/fm_paper_figure20.smt2");
			add("fm_paper/fm_paper_figure21.smt2");
			add("fm_paper/fm_paper_figure22.smt2");
			add("fm_paper/fm_paper_figure22_and.smt2");
			add("fm_paper/fm_paper_figure23_and.smt2");
			add("fm_paper/fm_paper_figure24.smt2");
			add("fm_paper/fm_paper_figure26.smt2");

			// Gobra.
			add("gobra/gobra_arrayWithNil1_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("gobra/gobra_arrayWithNil3_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("gobra/gobra_arrayWithNil5_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("gobra/gobra_arrayWithNil6_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("gobra/gobra_arrayWithNil7_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");

			// SMT-COMP.
			add("smt_comp/smt_comp_baby_53_reset_guest_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_havoc_bench_024_2_main_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_quant0_Test_MainX_System_optional_NonNullType_String_array_notnull_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_Quantifiers_Q_noinfer_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_Quantifiers_S_noinfer_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_Quantifiers_U0_noinfer_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_Quantifiers_U1_noinfer_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_Quantifiers_W_noinfer_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_Quantifiers_X0_noinfer_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_Quantifiers_X1_noinfer_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_Queue_c_3_enqueue_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_specsharp_WindowsCard_27_RTE_OpRET_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_specsharp_WindowsCard_35_RTE_MOpRET_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_specsharp_WindowsCard_41_RTE_MOpPOPA_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_specsharp_WindowsCard_4_Memory_set_cont_System_Int32_System_Byte_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_verisoft_memvirt_c_1_phys_mem_read_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_verisoft_memvirt_c_8_bl_mem_read_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_x2015_09_10_16_47_05_291_1010042_smt_in_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_x2015_09_10_16_49_52_978_1009894_smt_in_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_x2015_09_10_16_49_54_469_1011706_smt_in_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_x2015_09_10_16_57_40_818_1160163_smt_in_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_x2015_09_10_17_19_34_833_2884007_smt_in_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_textbook_CircularQueue_dll_11_CirQueue_EnQueue_System_Int32_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_vccp_queue_c_8_transfer_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_verisoft_sim_c_1_27_translated_read_sim_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_WindowsCard_c_11_init_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");

			// Viper.
			add("viper/viper_b0_vpr_typeEncoding_a_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("viper/viper_b7_vpr_typeEncoding_a_1_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("viper/viper_b10_2_vpr_typeEncoding_a_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
		};
	};

	// These are all the examples for which the Z3 API cannot generate an
	// unsat-proof on my machine (within the resources defined in the Setup class).
	public static LinkedList<String> removed_z3_benchmarks = new LinkedList<String>() {
		private static final long serialVersionUID = 7471968607553938708L;

		{
			// Test Set 2.
			add("fm_paper/fm_paper_figure01.smt2");
			add("fm_paper/fm_paper_figure04.smt2");
			add("fm_paper/fm_paper_figure04_fstar.smt2");
			add("fm_paper/fm_paper_figure12.smt2");
			add("fm_paper/fm_paper_figure18.smt2");

			// Dafny.
			add("dafny/dafny_issue134_std_unique_aug_gt_unsat_full_incomplete_quant_min.smt2");
			add("dafny/dafny_issue135_std_unique_aug_gt_unsat_full_incomplete_quant_min.smt2");
			add("dafny/dafny_seq_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("dafny/dafny_heap_succ_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");

			// F*.
			add("fstar/fstar_div_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("fstar/fstar_issue1595_std_unique_aug_gt_unsat_full_incomplete_quant_min.smt2");

			// Gobra.
			add("gobra/gobra_arrayWithNil2_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("gobra/gobra_arrayWithNil8_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("gobra/gobra_arrayWithNil9_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("gobra/gobra_arrayWithNil10_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("gobra/gobra_arrayWithNil11_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("gobra/gobra_option_wrong_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");

			// SMT-COMP.
			add("smt_comp/smt_comp_BinarySearchTree_c_3_Insert_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_havoc_bench_200_1_main_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_havoc_bench_subtype_6_Q1_bad_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_javafe_util_LocationManagerCorrelatedReader_001_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_PeerFields_Parent_N_astd_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_PeerFields_Parent_Q_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_PeerFields_PeerFields_Assign4_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_PeerFields_PeerFields_N_System_Int32_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_PeerFields_PeerFields_Ouch_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_PeerFields_PeerFields_P_System_Int32_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_PeerFields_PeerFields_Q_System_Int32_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_PeerFields_PeerFields_R_System_Int32_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_PeerFields_PeerFields_S_System_Int32_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_PeerModifiesClauses_Homeboy_R_level_2_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_SES_Atom_Write_System_IO_TextWriter_notnull_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_SES_Nary_CArgs_System_Cl_G_List_1_opt_MS_Cn_NNT_SES_Sx_notnull_System_Boolean_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_test14_CommandLineOptions_ssc_10_Microsoft_Boogie_CommandLineOptions_CommandLineParseState_GetNumericArgument_System_Double_ptr_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_test14_CommandLineOptions_ssc_8_Microsoft_Boogie_CommandLineOptions_CommandLineParseState_GetNumericArgument_System_Int32_ptr_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_test14_Xml_ssc_8_Microsoft_Boogie_XmlSink_WriteError_System_String_notnull_Microsoft_Boogie_IToken_notnull_Microsoft_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_test14_Xml_ssc_9_Microsoft_Boogie_XmlSink_WriteError_System_String_notnull_System_Compiler_Node_notnull_Microsoft_Boo_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_textbook_BinarySearchTree_dll_3_Node_Insert_System_Int32_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_textbook_MinimalSegmentSum_dll_1_C_MinSum_System_Int32_array_notnull_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_verisoft_baby_c_1_37_handle_pf_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_verisoft_sim_c_1_16_untranslated_write_sim_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_verisoft_memvirt_c_3_rot1_mem_read_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_specsharp_WindowsCard_8_RTE_ctor_System_Int32_array_notnull_System_Int32_System_Int32_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_specsharp_WindowsCard_19_RTE_OpLDA_System_Int32_System_Int32_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_x2015_09_10_16_46_49_217_988796_smt_in_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_x2015_09_10_16_46_50_391_990345_smt_in_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_x2015_09_10_16_47_06_339_1011401_smt_in_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_x2015_09_10_16_50_27_197_1131886_smt_in_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_x2015_09_10_16_51_19_008_1108991_smt_in_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_x2015_09_10_16_52_43_811_1130425_smt_in_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_x2015_09_10_16_54_46_764_1495036_smt_in_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_x2015_09_10_17_20_23_584_2921931_smt_in_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");

			// Viper.
			add("viper/viper_b8_4_alt_vpr_typeEncoding_a_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("viper/viper_b8_4_vpr_typeEncoding_a_2_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("viper/viper_b10_1_vpr_typeEncoding_a_1_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("viper/viper_b10_3_vpr_typeEncoding_a_1_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("viper/viper_b8_5_alt_vpr_typeEncoding_a_2_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("viper/viper_b8_5_vpr_typeEncoding_a_2_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
		};
	};

	private static LinkedList<String> successful_vampire_benchmarks = new LinkedList<String>() {
		private static final long serialVersionUID = 1002585401742729711L;

		{
			// Test Set 1.
			add("bachelor_thesis/example_application_of_four_nested_functions.smt2");
			add("bachelor_thesis/example_application_of_three_nested_functions.smt2");
			add("bachelor_thesis/example_application_of_two_nested_functions.smt2");
			add("bachelor_thesis/example_barber.smt2");
			add("bachelor_thesis/example_boogie.smt2");
			add("bachelor_thesis/example_combinations.smt2");
			add("bachelor_thesis/example_de_bruijn_index_0.smt2");
			add("bachelor_thesis/example_de_bruijn_index_1.smt2");
			add("bachelor_thesis/example_de_bruijn_index_2.smt2");
			add("bachelor_thesis/example_de_bruijn_index_3.smt2");
			add("bachelor_thesis/example_de_bruijn_index_4.smt2");
			add("bachelor_thesis/example_difference_of_three_quantified_variables_without_patterns.smt2");
			add("bachelor_thesis/example_difference_of_three_quantified_variables_with_patterns.smt2");
			add("bachelor_thesis/example_difference_of_two_quantified_variables.smt2");
			add("bachelor_thesis/example_foo.smt2");
			add("bachelor_thesis/example_infinite_possibilities.smt2");
			add("bachelor_thesis/example_infinite_possibilities_constrained.smt2");
			add("bachelor_thesis/example_just_booleans_with_pattern.smt2");
			add("bachelor_thesis/example_just_integers_with_pattern.smt2");
			add("bachelor_thesis/example_linked_list.smt2");
			add("bachelor_thesis/example_negated_quantifier.smt2");
			add("bachelor_thesis/example_nested_function_applications.smt2");
			add("bachelor_thesis/example_nested_quantifier.smt2");
			add("bachelor_thesis/example_no_quantifiers.smt2");
			add("bachelor_thesis/example_product_of_three_quantified_variables.smt2");
			add("bachelor_thesis/example_product_of_two_quantified_variables.smt2");
			add("bachelor_thesis/example_project_description.smt2");
			add("bachelor_thesis/example_project_proposal.smt2");
			add("bachelor_thesis/example_schroedingers_cat.smt2");
			add("bachelor_thesis/example_sequential_quantifiers_1.smt2");
			add("bachelor_thesis/example_sequential_quantifiers_2.smt2");
			add("bachelor_thesis/example_sequential_quantifiers_3.smt2");
			add("bachelor_thesis/example_sum_of_three_constants.smt2");
			add("bachelor_thesis/example_sum_of_three_quantified_variables.smt2");
			add("bachelor_thesis/example_sum_of_two_constants.smt2");
			add("bachelor_thesis/example_sum_of_two_quantified_variables.smt2");
			add("bachelor_thesis/example_survey.smt2");
			add("bachelor_thesis/example_thesis_overview_without_symmetry.smt2");
			add("bachelor_thesis/example_thesis_overview_with_symmetry.smt2");

			// Test Set 2.
			add("fm_paper/fm_paper_figure02.smt2");
			add("fm_paper/fm_paper_figure05.smt2");
			add("fm_paper/fm_paper_figure08.smt2");
			add("fm_paper/fm_paper_figure09.smt2");
			add("fm_paper/fm_paper_figure11.smt2");
			add("fm_paper/fm_paper_figure13.smt2");
			add("fm_paper/fm_paper_figure14.smt2");
			add("fm_paper/fm_paper_figure15.smt2");
			add("fm_paper/fm_paper_figure16.smt2");
			add("fm_paper/fm_paper_figure19.smt2");
			add("fm_paper/fm_paper_figure20.smt2");
			add("fm_paper/fm_paper_figure21.smt2");
			add("fm_paper/fm_paper_figure22.smt2");
			add("fm_paper/fm_paper_figure22_and.smt2");
			add("fm_paper/fm_paper_figure23_and.smt2");
			add("fm_paper/fm_paper_figure24.smt2");

			// Gobra.
			add("gobra/gobra_arrayWithNil1_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("gobra/gobra_arrayWithNil2_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("gobra/gobra_arrayWithNil3_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("gobra/gobra_arrayWithNil5_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("gobra/gobra_arrayWithNil6_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("gobra/gobra_arrayWithNil7_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("gobra/gobra_arrayWithNil8_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("gobra/gobra_arrayWithNil9_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("gobra/gobra_arrayWithNil10_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("gobra/gobra_arrayWithNil11_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("gobra/gobra_option_wrong_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");

			// SMT-COMP.
			add("smt_comp/smt_comp_quant0_Test_MainX_System_optional_NonNullType_String_array_notnull_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_Quantifiers_Q_noinfer_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_Quantifiers_S_noinfer_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_Quantifiers_U0_noinfer_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_Quantifiers_U1_noinfer_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_Quantifiers_W_noinfer_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_Quantifiers_X0_noinfer_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_Quantifiers_X1_noinfer_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
		};
	};

	// These are all the benchmarks for which our implementation failed in the sense
	// that Vampire generated an unsat-proof within the time limit, but we could not
	// create a potential example (it was usually unsat).
	public static LinkedList<String> unsuccessful_vampire_benchmarks = new LinkedList<String>() {
		private static final long serialVersionUID = 7357454456832492907L;

		{
			// Test Set 1.
			add("bachelor_thesis/example_extract_quantified_variables.smt2");

			// Test Set 2.
			add("fm_paper/fm_paper_figure06.smt2");
			add("fm_paper/fm_paper_figure07.smt2");
			add("fm_paper/fm_paper_figure17.smt2");
			add("fm_paper/fm_paper_figure18.smt2");

			// Dafny.
			add("dafny/dafny_seq_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");

			// Gobra.
			add("gobra/gobra_arrayWithNil1_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("gobra/gobra_arrayWithNil2_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("gobra/gobra_arrayWithNil3_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("gobra/gobra_arrayWithNil5_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("gobra/gobra_arrayWithNil6_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("gobra/gobra_arrayWithNil7_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("gobra/gobra_arrayWithNil8_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("gobra/gobra_arrayWithNil9_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("gobra/gobra_arrayWithNil10_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("gobra/gobra_arrayWithNil11_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("gobra/gobra_option_wrong_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");

			// SMT-COMP.
			add("smt_comp/smt_comp_baby_53_reset_guest_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_BinarySearchTree_c_3_Insert_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_havoc_bench_024_2_main_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_havoc_bench_200_1_main_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_havoc_bench_subtype_6_Q1_bad_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_javafe_util_LocationManagerCorrelatedReader_001_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_PeerFields_Parent_N_astd_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_PeerFields_Parent_Q_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_Quantifiers_Q_noinfer_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_Queue_c_3_enqueue_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_SES_Atom_Write_System_IO_TextWriter_notnull_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_SES_Nary_CArgs_System_Cl_G_List_1_opt_MS_Cn_NNT_SES_Sx_notnull_System_Boolean_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_specsharp_WindowsCard_19_RTE_OpLDA_System_Int32_System_Int32_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_specsharp_WindowsCard_27_RTE_OpRET_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_specsharp_WindowsCard_35_RTE_MOpRET_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_specsharp_WindowsCard_41_RTE_MOpPOPA_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_specsharp_WindowsCard_4_Memory_set_cont_System_Int32_System_Byte_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_specsharp_WindowsCard_8_RTE_ctor_System_Int32_array_notnull_System_Int32_System_Int32_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_test14_CommandLineOptions_ssc_10_Microsoft_Boogie_CommandLineOptions_CommandLineParseState_GetNumericArgument_System_Double_ptr_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_test14_CommandLineOptions_ssc_8_Microsoft_Boogie_CommandLineOptions_CommandLineParseState_GetNumericArgument_System_Int32_ptr_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_test14_Xml_ssc_8_Microsoft_Boogie_XmlSink_WriteError_System_String_notnull_Microsoft_Boogie_IToken_notnull_Microsoft_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_test14_Xml_ssc_9_Microsoft_Boogie_XmlSink_WriteError_System_String_notnull_System_Compiler_Node_notnull_Microsoft_Boo_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_textbook_BinarySearchTree_dll_3_Node_Insert_System_Int32_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_textbook_CircularQueue_dll_11_CirQueue_EnQueue_System_Int32_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_textbook_MinimalSegmentSum_dll_1_C_MinSum_System_Int32_array_notnull_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_vccp_queue_c_8_transfer_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_verisoft_baby_c_1_37_handle_pf_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_verisoft_memvirt_c_1_phys_mem_read_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_verisoft_memvirt_c_3_rot1_mem_read_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_verisoft_memvirt_c_8_bl_mem_read_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_verisoft_sim_c_1_16_untranslated_write_sim_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_verisoft_sim_c_1_27_translated_read_sim_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_WindowsCard_c_11_init_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_x2015_09_10_16_46_49_217_988796_smt_in_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_x2015_09_10_16_46_50_391_990345_smt_in_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_x2015_09_10_16_47_05_291_1010042_smt_in_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_x2015_09_10_16_47_06_339_1011401_smt_in_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_x2015_09_10_16_49_52_978_1009894_smt_in_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_x2015_09_10_16_49_54_469_1011706_smt_in_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_x2015_09_10_16_50_27_197_1131886_smt_in_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_x2015_09_10_16_51_19_008_1108991_smt_in_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_x2015_09_10_16_52_43_811_1130425_smt_in_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_x2015_09_10_16_54_46_764_1495036_smt_in_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_x2015_09_10_16_57_40_818_1160163_smt_in_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_x2015_09_10_17_19_34_833_2884007_smt_in_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_x2015_09_10_17_20_23_584_2921931_smt_in_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");

			// Viper.
			add("viper/viper_b0_vpr_typeEncoding_a_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("viper/viper_b2_vpr_typeEncoding_a_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("viper/viper_b3_vpr_typeEncoding_a_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("viper/viper_b4_vpr_typeEncoding_a_1_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("viper/viper_b7_vpr_typeEncoding_a_1_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("viper/viper_b8_2_vpr_typeEncoding_a_2_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("viper/viper_b8_3_alt_vpr_typeEncoding_a_1_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("viper/viper_b8_3_vpr_typeEncoding_a_2_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("viper/viper_b8_4_alt_vpr_typeEncoding_a_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("viper/viper_b8_4_vpr_typeEncoding_a_2_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("viper/viper_b8_5_alt_vpr_typeEncoding_a_2_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("viper/viper_b8_5_vpr_typeEncoding_a_2_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("viper/viper_b10_1_vpr_typeEncoding_a_1_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("viper/viper_b10_2_vpr_typeEncoding_a_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("viper/viper_b10_3_vpr_typeEncoding_a_1_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
		};
	};

	// These are all the for which the Z3 API cannot generate an unsat-proof on my
	// machine (within the resources defined in the Setup class).
	public static LinkedList<String> removed_vampire_benchmarks = new LinkedList<String>() {
		private static final long serialVersionUID = -5381833656075991167L;

		{
			// Test Set 2.
			add("fm_paper/fm_paper_figure01.smt2");
			add("fm_paper/fm_paper_figure04.smt2");
			add("fm_paper/fm_paper_figure04_fstar.smt2");
			add("fm_paper/fm_paper_figure12.smt2");

			// Dafny.
			add("dafny/dafny_issue134_std_unique_aug_gt_unsat_full_incomplete_quant_min.smt2");
			add("dafny/dafny_issue135_std_unique_aug_gt_unsat_full_incomplete_quant_min.smt2");
			add("dafny/dafny_seq_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");

			// F*.
			add("fstar/fstar_div_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("fstar/fstar_issue1595_std_unique_aug_gt_unsat_full_incomplete_quant_min.smt2");

			// SMT-COMP.
			add("smt_comp/smt_comp_PeerFields_PeerFields_Assign4_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_PeerFields_PeerFields_N_System_Int32_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_PeerFields_PeerFields_Ouch_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_PeerFields_PeerFields_P_System_Int32_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_PeerFields_PeerFields_Q_System_Int32_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_PeerFields_PeerFields_R_System_Int32_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_PeerFields_PeerFields_S_System_Int32_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_PeerModifiesClauses_Homeboy_R_level_2_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
			add("smt_comp/smt_comp_quant0_Test_MainX_System_optional_NonNullType_String_array_notnull_std_unique_aug_gt_unsat_full_incomplete_quant.smt2");
		};
	};
}