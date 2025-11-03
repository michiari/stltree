#!/usr/bin/env python3

import sys
import os
sys.path.append(os.getcwd())

import time
from wrapt_timeout_decorator import *
from fractions import Fraction

from stl_consistency.parser import STLParser, normalize_bounds
from stl_consistency.node import Node
from stl_consistency.smtchecker import smt_check_consistency
from stl_consistency.qsmtchecker import qsmt_check_consistency
from stl_consistency.tableau import make_tableau

import csv
from tabulate import tabulate
import networkx as nx

@timeout(dec_timeout='args[0]', dec_allow_eval=True, use_signals=False)
def inner(timeout, f, *args, **kwargs):
    return f(*args, **kwargs)

def run_with_timeout(timeout, f, *args, **kwargs):
    try:
        return inner(timeout, f, *args, **kwargs)
    except TimeoutError as e:
        print(e)
        return "timeout"


# Benchmark: (avionics requirements)
# 1) time horizon (T)
T = str(1000)
requirements = [
    ['G', '0', T, ['||', ['&&', ['active'], ['!', ['inactive']], ['!', ['armed']]], ['&&', ['inactive'], ['!', ['active']], ['!', ['armed']]], ['&&', ['armed'], ['!', ['inactive']], ['!', ['active']]]]],
    ['G', '0', T, ['->', ['&&', ['inactive'], ['n_s == 1'],  ['X_c-X_b <= 5'], ['X_c-X_b>= -5'], ['G', '0', '5', ['airspeed>= Vmin']], ['!', ['X_over']], ['X_Activation_Request']], ['F', '0', '2', ['&&', ['!', ['inactive']], ['active']]]]],
    ['G', '0', T, ['->', ['&&', ['active'], ['||', ['!', ['n_s == 1']], ['F', '0', '10', ['X_ch']], ['G', '0', '5', ['airspeed < Vmin']],  ['!', ['r_actuation']], ['!', ['X_Activation_Request']]]], ['F', '0', '2', ['&&', ['!', ['active']], ['inactive']]]]],
    ['G', '0', T, ['->', ['&&', ['armed'], ['||', ['!', ['n_s ==1']], ['F', '0', '5', ['X_ch']], ['!', ['X_Activation_Request']], ['!', ['r_actuation']]]], ['F', '0', '2', ['&&', ['!', ['armed']], ['inactive']]]]],
    ['G', '0', T, ['->', ['&&', ['inactive'], ['n_s ==1'], ['||', ['X_c - X_b >5'], ['X_c - X_b <-5']], ['X_Activation_Request']], ['F', '0', '2', ['&&', ['!', ['inactive']], ['armed']]]]],
    ['G', '0', T, ['->', ['&&', ['armed'], ['!', ['X_over']], ['X_c - X_b <=5'], ['X_c - X_b >=-5'], ['G', '0', '5', ['airspeed >= Vmin']]], ['F', '0', '2', ['&&', ['!', ['armed']], ['active']]]]], #DOPPIONE (dovrebbe essere stato corretto=
    ['G', '0', T, ['||', ['&&', ['active'], ['A']], ['&&', ['active'], ['B']], ['&&', ['active'], ['C']]]],
    ['G', '0', T, ['->', ['&&', ['active'], ['A'], ['!', ['X_over']], ['Delta_T_Error_reference < T_Error'], ['Delta_T_Error_reference > 0 - T_Error']], ['F', '0', '1', ['&&', ['!', ['A']], ['B']]]]],
    ['G', '0', T, ['->', ['&&', ['active'], ['B'], ['!', ['X_over']], ['T_Error < 3'], ['T_Error  > -3'],  ['Roll_attitude < 0.8'], ['Roll_attitude > -0.8'],  ['X_deviation < 0.5'], ['X_deviation > -0.5'], ['dalfadt < 0.002'], ['dalfadt > -0.002'], ['!', ['h_on']], ['!', ['f_on']]], ['F', '0', '1', ['&&', ['!', ['B']], ['C']]]]],
    ['G', '0', T, ['->', ['&&', ['active'], ['C'], ['!', ['X_over']], ['||', ['T_Error > 5'], ['T_Error < -5']], ['||', ['Roll_attitude > 2.6'], ['Roll_attitude < -2.6']], ['||', ['X_deviation > 1.5'], ['X_deviation < -1.5']], ['||', ['dalfadt > 0.075'], ['dalfadt < -0.075']], ['||', ['h_on'], ['f_on']]], ['F', '0', '1', ['&&', ['!', ['C']], ['B']]]]],
    ['G', '0', T, ['->', ['&&', ['active'], ['!', ['X_over']]], ['F', '0', '5', ['LME_cr == 1']]]],
    ['G', '0', T, ['->', ['inactive'], ['F', '0', '5', ['LME_cr == 0']]]],
    ['G', '0', T, ['->', ['armed'], ['F', '0', '5', ['LMA_cr == 1']]]],
    ['G', '0', T, ['->', ['active'], ['F', '0', '5', ['&&', ['LMT_ar'], ['a_tone']]]]],
    ['G', '0', T, ['->', ['inactive'], ['F', '0', '5', ['&&', ['LMT_ar'], ['a_tone']]]]],
    ['G', '0', T, ['->', ['X_over'], ['F', '0', '5', ['&&', ['LMT_ar'], ['a_tone']]]]],
    ['G', '0', T, ['->', ['&&', ['X_over'], ['active']], ['F', '0', '5', ['LME_cr == 1']]]],
    ['G', '0', T, ['->', ['active'], ['F', '0', '1', ['Y_pushbutton == 1']]]],
    ['G', '0', T, ['->', ['armed'], ['F', '0', '1', ['Y_pushbutton == 2']]]],
    ['G', '0', T, ['->', ['airspeed < Vmin'], ['F', '0', '5', ['LS_amr']]]],
]

requirements_riscritti = [
    ['G', '0', T, ['||', ['function_status == 0'], ['function_status == 1'], ['function_status == 2']]], #where 0 == inactive, 1==armed, 2==active
    ['G', '0', T, ['->', ['&&', ['function_status == 0'], ['n_s == 1'],  ['|X_c - X_b| <= 5'], ['G', '0', '5', ['airspeed >= Vmin']], ['!', ['X_over']], ['X_Activation_Request']], ['F', '1', '2', ['function_status == 2']]]],
    ['G', '0', T, ['->', ['&&', ['function_status == 2'], ['||', ['!', ['n_s == 1']], ['F', '0', '10', ['X_ch']], ['G', '0', '5', ['airspeed < Vmin']], ['!', ['r_actuation']], ['!', ['X_Activation_Request']]]], ['F', '1', '2', ['function_status == 0']]]],
    ['G', '0', T, ['->', ['&&', ['function_status == 1'], ['||', ['!', ['n_s == 1']], ['F', '0', '5', ['X_ch']], ['!', ['X_Activation_Request']], ['!', ['r_actuation']]]], ['F', '1', '2', ['function_status == 0']]]],
    ['G', '0', T, ['->', ['&&', ['function_status == 0'], ['n_s == 1'], ['|X_c - X_b| > 5'], ['X_Activation_Request']], ['F', '1', '2', ['function_status == 1']]]],
    ['G', '0', T, ['->', ['&&', ['function_status == 1'], ['!', ['X_over']], ['|X_c - X_b| <= 5'], ['G', '0', '5', ['airspeed >= Vmin']]], ['F', '1', '2', ['function_status == 2']]]],
    ['G', '0', T, ['->', ['function_status == 2'], ['||', ['function_active_status == 0'], ['function_active_status == 1'], ['function_active_status == 2']]]],
    ['G', '0', T, ['->', ['&&', ['function_active_status == 0'], ['!', ['X_over']], ['|Delta_T_Error_reference| < T_Error']], ['F', '1', '2', ['function_active_status == 1']]]],
    ['G', '0', T, ['->', ['&&', ['function_active_status == 1'], ['!', ['X_over']], ['|T_Error| < 3'], ['|Roll_attitude| < 0.8'], ['|X_deviation| < 0.5'], ['|dalfadt| < 0.002'], ['!', ['h_on']], ['!', ['f_on']]], ['F', '1', '2', ['function_active_status == 2']]]],
    ['G', '0', T, ['->', ['&&', ['function_active_status == 2'], ['!', ['X_over']], ['|T_Error| > 5'], ['|Roll_attitude| > 2.6'], ['|X_deviation| > 1.5'], ['|dalfadt| > 0.075'], ['||', ['h_on'], ['f_on']]], ['F', '1', '2', ['function_active_status == 1']]]],
    ['G', '0', T, ['->', ['&&', ['function_status == 2'], ['!', ['X_over']]], ['F', '0', '5', ['LME_cr == 1']]]],
    ['G', '0', T, ['->', ['function_status == 0'], ['F', '0', '5', ['LME_cr == 0']]]],
    ['G', '0', T, ['->', ['function_status == 1'], ['F', '0', '5', ['LMA_cr == 1']]]],
    ['G', '0', T, ['->', ['function_status == 2'], ['F', '0', '5', ['&&', ['LMT_ar'], ['a_tone']]]]],
    ['G', '0', T, ['->', ['function_status == 0'], ['F', '0', '5', ['&&', ['LMT_ar'], ['a_tone']]]]],
    ['G', '0', T, ['->', ['X_over'], ['F', '0', '5', ['&&', ['LMT_ar'], ['a_tone']]]]],
    ['G', '0', T, ['->', ['&&', ['X_over'], ['function_status == 2']], ['F', '0', '5', ['LME_cr == 1']]]],
    ['G', '0', T, ['->', ['function_status == 2'], ['F', '0', '1', ['Y_pushbutton == 1']]]],
    ['G', '0', T, ['->', ['function_status == 1'], ['F', '0', '1', ['Y_pushbutton == 2']]]],
    ['G', '0', T, ['->', ['airspeed < Vmin'], ['F', '0', '5', ['LS_amr']]]],
]

requirements_riscritti2 = [['G', '0', T, ['&&', ['||', ['function_status == 0'], ['function_status == 1'], ['function_status == 2']],['->', ['&&', ['function_status == 0'], ['n_s == 1'],  ['|X_c - X_b| <= 5'], ['G', '0', '5', ['airspeed >= Vmin']], ['!', ['X_over']], ['X_Activation_Request']], ['F', '1', '2', ['function_status == 2']]],['->', ['&&', ['function_status == 2'], ['||', ['!', ['n_s == 1']], ['F', '0', '10', ['X_ch']], ['G', '0', '5', ['airspeed < Vmin']], ['!', ['r_actuation']], ['!', ['X_Activation_Request']]]], ['F', '1', '2', ['function_status == 0']]],['->', ['&&', ['function_status == 1'], ['||', ['!', ['n_s == 1']], ['F', '0', '5', ['X_ch']], ['!', ['X_Activation_Request']], ['!', ['r_actuation']]]], ['F', '1', '2', ['function_status == 0']]],['->', ['&&', ['function_status == 0'], ['n_s == 1'], ['|X_c - X_b| > 5'], ['X_Activation_Request']], ['F', '1', '2', ['function_status == 1']]],['->', ['&&', ['function_status == 1'], ['!', ['X_over']], ['|X_c - X_b| <= 5'], ['G', '0', '5', ['airspeed >= Vmin']]], ['F', '1', '2', ['function_status == 2']]],['->', ['function_status == 2'], ['||', ['function_active_status == 0'], ['function_active_status == 1'], ['function_active_status == 2']]],['->', ['&&', ['function_active_status == 0'], ['!', ['X_over']], ['|Delta_T_Error_reference| < T_Error']], ['F', '1', '2', ['function_active_status == 1']]],['->', ['&&', ['function_active_status == 1'], ['!', ['X_over']], ['|T_Error| < 3'], ['|Roll_attitude| < 0.8'], ['|X_deviation| < 0.5'], ['|dalfadt| < 0.002'], ['!', ['h_on']], ['!', ['f_on']]], ['F', '1', '2', ['function_active_status == 2']]],['->', ['&&', ['function_active_status == 2'], ['!', ['X_over']], ['|T_Error| > 5'], ['|Roll_attitude| > 2.6'], ['|X_deviation| > 1.5'], ['|dalfadt| > 0.075'], ['||', ['h_on'], ['f_on']]], ['F', '1', '2', ['function_active_status == 1']]],['->', ['&&', ['function_status == 2'], ['!', ['X_over']]], ['F', '0', '5', ['LME_cr == 1']]],['->', ['function_status == 0'], ['F', '0', '5', ['LME_cr == 0']]],['->', ['function_status == 1'], ['F', '0', '5', ['LMA_cr == 1']]],['->', ['function_status == 2'], ['F', '0', '5', ['&&', ['LMT_ar'], ['a_tone']]]],['->', ['function_status == 0'], ['F', '0', '5', ['&&', ['LMT_ar'], ['a_tone']]]],['->', ['X_over'], ['F', '0', '5', ['&&', ['LMT_ar'], ['a_tone']]]],['->', ['&&', ['X_over'], ['function_status == 2']], ['F', '0', '5', ['LME_cr == 1']]],['->', ['function_status == 2'], ['F', '0', '1', ['Y_pushbutton == 1']]],['->', ['function_status == 1'], ['F', '0', '1', ['Y_pushbutton == 2']]],['->', ['airspeed < Vmin'], ['F', '0', '5', ['LS_amr']]]]]]

parameter_ranges = [
    ['G', '0', T, ['&&', ['X_c >=0'], ['X_c <= 360']]],
    ['G', '0', T, ['&&', ['X_b >=0'], ['X_b <= 360']]],
    ['G', '0', T, ['&&', ['airspeed >=0'], ['airspeed <= 200']]],
    ['G', '0', T, ['&&', ['a >= 0'], ['a <= 360']]],
    ['G', '0', T, ['||', ['n_s == 0'], ['n_s == 1'], ['n_s == 2']]],
    ['G', '0', T, ['|T_Error| <= 180']],
    ['G', '0', T, ['|Roll_attitude| <= 50']],
    ['G', '0', T, ['|X_deviation| <= 180']],
    ['G', '0', T, ['||', ['LME_cr == 0'], ['LME_cr == 1'], ['LME_cr == 2']]],
    ['G', '0', T, ['||', ['LMA_cr == 0'], ['LMA_cr == 1'], ['LMA_cr == 2']]],
    ['G', '0', T, ['||', ['Y_pushbutton == 0'], ['Y_pushbutton == 1'], ['Y_pushbutton == 2']]],
]


#Requirements from: Benchmarks for Temporal Logic Requirements for Automotive Systems
t = '10'
T1 = '1000'
mtl_requirements = [
    ['G', '0', T1, ['&&', ['omega < omega_hat'], ['v < v_hat']]],
    ['G', '0', T1, ['->', ['&&', ['g2'], ['G', '1', '1', ['g1']]], ['G', '0.5', '2.5', ['!', ['g2']]]]],
    ['G', '0', T1, ['->', ['&&', ['!', ['g1']], ['G', '1', '1', ['g1']]], ['G', '0.5', '2.5', ['g1']]]],
    ['G', '0', T1, ['->', ['&&', ['!', ['g2']], ['G', '1', '1', ['g2']]], ['G', '0.5', '2.5', ['g2']]]],
    ['G', '0', T1, ['->', ['&&', ['!', ['g3']], ['G', '1', '1', ['g3']]], ['G', '0.5', '2.5', ['g3']]]],
    ['G', '0', T1, ['->', ['&&', ['!', ['g4']], ['G', '1', '1', ['g4']]], ['G', '0.5', '2.5', ['g4']]]],
    ['!', ['&&', ['F', '0', t, ['v > v_hat']], ['G', '0', T1, ['omega < omega_hat']]]],
    ['F', '0', t, ['&&', ['v >= v_hat'], ['G', '0', T1, ['omega < omega_hat']]]],
    ['F', '0', '100', ['G', '0', '1', ['!', ['Fuel_Flow_Rate == 0']]]],
    ['G', '0', T1, ['->', ['lambda_OOB'], ['F', '0', '1', ['G', '0', '1', ['!', ['lambda_OOB']]]]]]

]

#Requirements from: Powertrain Control Verification Benchmark
T3 = '15'
epsilon = '0.02'
t_s = '11'
eta = '1'
zeta_mezzi = '10'
pcv = [
    # normal mode
    ['G', '0', T3, ['->', ['normal_mode'], ['&&', ['a > 8.8'], ['a < 70']]]],
    ['G', t_s, T3, ['->', ['normal_mode'], ['|mu| < 0.05']]],
    ['G', t_s, T3, ['->', ['||', ['&&', ['theta == 8.8'], ['F', '0', epsilon, ['theta == a']]], ['&&', ['theta == a'], ['F', '0', epsilon, ['theta == 8.8']]]], ['G', eta, zeta_mezzi, ['|mu| < 0.02']]]],
    ['F', T3, T3, ['->', ['normal_mode'], ['xrms < 0.05']]],
    ['G', t_s, T3, ['->', ['normal_mode'], ['|mu| < 0.1']]],
    #power mode
    ['G', '0', T3, ['->', ['power_mode'], ['&&', ['a >= 8.8'], ['a <= 90']]]],
    ['G', t_s, T3, ['->', ['&&', ['power_mode'], ['F', '0', epsilon, ['normal_mode']]], ['G', eta, zeta_mezzi, ['|mu| < 0.02']]]],
    ['G', t_s, T3, ['->', ['power_mode'], ['|mu_p| < 0.2']]],
    # startup and sensor fail mode
    ['G', '0', T3, ['->', ['&&', ['||', ['startup_mode'], ['sensor_fail_mode']], ['||', ['&&', ['theta == 8.8'], ['F', '0', epsilon, ['theta == a']]], ['&&', ['theta == a'], ['F', '0', epsilon, ['theta == 8.8']]]]], ['G', eta, zeta_mezzi, ['|mu| < 0.1']]]]
]

#Requirements from Signal-Based Properties of Cyber-Physical Systems: Taxonomy and Logic-based Characterization
T2 = '3000'
req_cps = [
    ['G', '0', T2, ['||', ['currentADCSMode == 0'], ['currentADCSMode == 1'], ['currentADCSMode == 2']]], # P1 where 0 == NMC, 1== NMF, 2== SM
    ['G', '0', T2, ['RWs_angular_velocity == 816.814']], # P4
    ['G', '2000', T2, ['pointing_error < 2']], # P5
    ['G', '1500', '2000', ['RWs_angular_momentum < 0.35']], # P6
    ['G', '2000', '2000', ['&&', ['pointing_error > 0'], ['pointing_error < delta']]], # P7 delta???
    ['F', '2000', '7400', ['&&', ['pointing_error < k'], ['U', '2', '22', ['pointing_error >= k'], ['pointing_error < k']]]], # P8 SPIKE
    #[], # P9 OSCILLATION
    ['G', '0', T2, ['|sat_init_angular_velocity_degree| <= 3']], # P10
    ['G', '2000', T2, ['|sat_real_angular_velocity| <= 1.5']], # P11
    ['G', '0', T2, ['||', ['sat_target_attitude == 1'], ['sat_target_attitude == -1']]], # P12
    ['G', '2000', T2, ['|sat_target_angular_velocity| <= 1.5']], # P13
    ['G', '0', T2, ['||', ['sat_estimated_attitude == 1'], ['sat_estimated_attitude == -1']]], # P14
    ['G', '2000', T2, ['|sat_estimated_angular_velocity| <= 1.5']], # P15
    ['G', '2000', T2, ['|sat_angular_velocity_measured| <= 1.5']], # P16
    ['G', '0', T2, ['|earth_mag_field_in_body_measured| <= 60000']], # P17
    ['G', '0', T2, ['||', ['sun_direction_ECI == 1'], ['sun_direction_ECI == -1']]], # P18
    ['G', '2000', T2, ['|sat_target_angular_velocity_safe_spin_mode| <= 1.5']], # P19
    ['G', '0', T2, ['|RWs_torque| <= 0.015']], # P20
    ['G', '0', T2, ['sun_sensor_availability <= 3']], # P21
    ['G', '2000', '2000', ['&&', ['q_real - q_estimate_attitude > 0'], ['q_real - q_estimate_attitude < delta']]], # P22
    ['G', '2000', '2000', ['&&', ['q_target_attitude - q_estimate > 0'], ['q_target_attitude - q_estimate < delta']]], # P23
    ['G', '0', T2, ['&&', ['sat_estimated_angular_velocity - sat_real_angular_velocity > 0'], ['sat_estimated_angular_velocity - sat_real_angular_velocity < delta']]], # P24
    ['G', '0', T2, ['&&', ['sat_angular_velocity_measured - sat_real_angular_velocity > 0'], ['sat_angular_velocity_measured - sat_real_angular_velocity < delta']]], # P25
    #[], # P26 derivative?
    ['G', '0', T2, ['->', ['!', ['not_Eclipse']], ['!', ['sun_currents']]]], # P27
    ['G', '0', T2, ['->', ['pointing_error_under_15'], ['!', ['pointing_error_above_20']]]], # P28
    ['G', '0', T2, ['->', ['pointing_error_above_20'], ['!', ['pointing_error_under_15']]]], # P29
    ['G', '0', T2, ['->', ['RWs_command == 0'], ['F', '0', '60', ['RWs_angular_velocity == 0']]]], # P30
    ['G', '0', T2, ['->', ['RWs_angular_momentum > 0.35'], ['RWs_torque == 0']]], # P31
    ['G', '0', T2, ['->', ['currentADCSMode == 0'], ['control_error >= 10']]], # P32
    ['G', '0', T2, ['->', ['control_error < 10'], ['currentADCSMode == 1']]], # P33
    ['G', '0', T2, ['->', ['currentADCSMode == 1'], ['control_error <= 15']]], # P34
    ['G', '0', T2, ['->', ['currentADCSMode == 1'], ['->', ['RWs_command > 0'], ['F', '0', '180', ['pointing_error < 2']]]]], # P35
    ['G', '0', T2, ['->', ['currentADCSMode == 1'], ['->', ['RWs_command > 0'], ['F', '0', '180', ['control_error < 0.5']]]]], # P36
    ['G', '0', T2, ['->', ['currentADCSMode == 1'], ['->', ['not_Eclipse'], ['F', '0', '900', ['knowledge_error < 1']]]]], # P37
    ['G', '0', T2, ['->', ['currentADCSMode == 2'], ['->', ['RWs_command > 0'], ['F', '0', '900', ['RWs_angular_momentum < 0.25']]]]], # P38
    ['G', '0', T2, ['->', ['currentADCSMode == 2'], ['F', '0', '10799', ['real_Omega - signal_target_Omega == 0']]]], # P39
    ['G', '0', T2, ['->', ['not_Eclipse'], ['sun_angle < 45']]], # P40
    ['G', '1600', T2, ['->', ['pointing_error < 2'], ['F', '0', '5400', ['&&', ['pointing_error < k2'], ['U', '0', '600', ['pointing_error >= k'], ['pointing_error < k2']]]]]] # P41
]

#Requirements from Bounded Model Checking of STL Properties using Syntactic Separation
cars = [
    ['G', '0', '100', ['dist > 0.1']],
    ['G', '0', '20', ['->', ['dist < 6'], ['F', '0', '15', ['acc2']]]],
    ['F', '12', '20', ['->', ['dec2'], ['F', '3', '18', ['acc2']]]],
    ['F', '4', '40', ['U', '10', '20', ['dec2'], ['&&', ['|x| <= 0.5'], ['|y| <= 0.5']]]]
]

thermostat = [
    ['G', '0', '40', ['x1 <= 21']],
    ['G', '0', '10', ['U', '0', '5', ['x2 > 20'], ['on1']]],
    ['G', '0', '20', ['R', '2', '12', ['x2 > 20'], ['x1 < 10']]],
    ['F', '0', '20', ['->', ['&&', ['off1'], ['off2']], ['G', '0', '5', ['||', ['on1'], ['on2']]]]]
]

watertank = [
    ['G', '0', '50', ['&&', ['x1 > 0'], ['x1 <= 9'], ['x2 > 0'], ['x2 <= 9']]],
    ['G', '0', '10', ['->', ['x1 < 4.9'], ['F', '0', '10', ['x1 >= 5.1']]]],
    ['F', '5', '14', ['->', ['off1'], ['F', '0', '7', ['&&', ['on1'], ['x1 > 5.5']]]]],
    ['G', '0', '20', ['->', ['&&', ['on1'], ['on2']], ['F', '0', '5', ['||', ['off1'], ['off2']]]]]

]

railroad = [
    ['F', '1', '49', ['pos <= 0']],
    ['G', '20', '40', ['->', ['angle >= 80'], ['F', '1', '20', ['pos <= 0']]]],
    ['G', '3', '50', ['F', '5', '20', ['angle >= 80']]],
    ['G', '10', '60', ['->', ['angle >= 80'], ['G', '20', '40', ['angle < 60']]]]
]

batteries = [
    ['G', '1', '20', ['F', '3', '14', ['d1 >= 1.4']]],
    ['F', '6', '30', ['->', ['&&', ['live1'], ['live2']], ['G', '7', '24', ['&&', ['live1'], ['live2']]]]],
    ['G', '1', '49', ['&&', ['d1 > 0.5'], ['d2 > 0.5']]],
    ['G', '11', '50', ['U', '2', '14', ['||', ['g1 >= 0'], ['g2 >= 0']], ['&&', ['dead1'], ['dead2']]]]
]


# Test stuff (do not remove pls!)

# railroad = [
#     ['G', '3', '50', ['F', '5', '20', ['a']]],
#     ['G', '10', '60', ['->', ['a'], ['G', '20', '40', ['!', ['a']]]]]
# ]

# railroad = [
#     ['G', '0', '10', ['F', '0', '5', ['a']]],
#     ['G', '0', '6', ['->', ['a'], ['G', '3', '8', ['!', ['a']]]]]
# ]

railroad_merged = [
    ['G', '3', '9', ['F', '5', '20', ['a']]],
    ['G', '10', '50', ['||', ['&&', ['F', '5', '20', ['a']], ['!', ['a']]], ['&&', ['F', '5', '20', ['a']], ['G', '20', '40', ['!', ['a']]]]]],
    ['G', '51', '60', ['||', ['!', ['a']], ['G', '20', '40', ['!', ['a']]]]]
]

example = [
    ['&&',
        ['G', '0', '10', ['x > 5']],
        ['F', '0', '11', ['x < 0']]
    ]
]


def make_and(formulas):
    if len(formulas) == 1:
        return formulas[0]
    return ['&&'] + formulas

datasets = {
    "cars": cars,
    "thermostat": thermostat,
    "watertank": watertank,
    "railroad": railroad,
    "batteries": batteries,
    "pcv": pcv,
    "mtl_requirements": mtl_requirements,
    "req_cps": req_cps,
    "avionics": requirements_riscritti2 + parameter_ranges,
}

# Funzione per eseguire entrambi i test su un dataset
def check_dataset(dataset_name, dataset, max_depth, mode, max_quantum, timeout, iters):
    # Formula
    formula = make_and(dataset)
    parser = STLParser()
    parsed_formula = parser.parse_relational_exprs(formula)
    normalized_formula = normalize_bounds(parsed_formula, max_quantum)

    # SMT
    start_t = time.perf_counter()
    for _ in range(iters):
        res_smt = run_with_timeout(timeout, smt_check_consistency, normalized_formula, mode, False, False)
        if res_smt == 'timeout':
            elapsed_smt = timeout
            break
    else:
        elapsed_smt = (time.perf_counter() - start_t) / iters

    # Quantified SMT
    start_t = time.perf_counter()
    for _ in range(iters):
        res_qsmt = run_with_timeout(timeout, qsmt_check_consistency, normalized_formula, False, False)
        if res_qsmt == 'timeout':
            elapsed_qsmt = timeout
            break
    else:
        elapsed_qsmt = (time.perf_counter() - start_t) / iters

    # Tableau
    start_t = time.perf_counter()
    for _ in range(iters):
        res_tableau = run_with_timeout(timeout, make_tableau, Node(*normalized_formula), max_depth, mode, False, False, False, False, False)
        #res_tableau = make_tableau(Node(*normalized_formula), max_depth, mode, False, False, False, False)
        if res_tableau == 'timeout':
            elapsed_tableau = timeout
            break
    else:
        elapsed_tableau = (time.perf_counter() - start_t) / iters
    
    # print(len(res_tableau[0]))
    #nx.drawing.nx_pydot.write_dot(res_tableau[0], './example.dot')

    # Dizionario con i risultati
    return {
        'dataset': dataset_name,
        'time_smt': elapsed_smt,
        'result_smt': res_smt,
        'time_qsmt': elapsed_qsmt,
        'result_qsmt': res_qsmt,
        'time_tableau': elapsed_tableau,
        'result_tableau': res_tableau
    }

# Print results
def pretty_print(results, ms, csvfile):
    timeh, timef = ("Time (ms)", lambda t: t * 1000) if ms else ("Time (s)", lambda x: x)

    # Table
    results_matrix = [
        [r['dataset'], timef(r['time_smt']), r['result_smt'], timef(r['time_qsmt']), r['result_qsmt'], timef(r['time_tableau']), r['result_tableau']]
        for r in results
    ]

    # Columns in table
    header = ["Dataset", f"SMT {timeh}", "SMT Result", f"QSMT {timeh}", "QSMT Result", f"Tableau {timeh}", "Tableau Result"]

    print(tabulate(results_matrix, headers=header))

    if csvfile:
        with open(csvfile, 'w', newline='') as f:
            cw = csv.writer(f)
            cw.writerow(header)
            cw.writerows(results_matrix)

# Main execution
if __name__ == '__main__':
    sys.setrecursionlimit(1000000000)
    max_depth = 10000000
    mode = 'sat' # 'strong_sat'
    sampling_interval = 1 # Fraction(1,10)
    timeout = 120 # in seconds
    iterations = 5

    results = [check_dataset(name, data, max_depth, mode, sampling_interval, timeout, iterations) for name, data in datasets.items()]

    print("Benchmark results:")
    pretty_print(results, ms=False, csvfile="results.csv")
