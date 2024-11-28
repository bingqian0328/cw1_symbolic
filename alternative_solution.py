#This code is the alternative solution implemented using OR-Toolspyth
import os
from ortools.sat.python import cp_model
import re
import time 

class Instance:
    def __init__(self):
        self.number_of_students = 0
        self.number_of_exams = 0
        self.number_of_slots = 0
        self.number_of_rooms = 0
        self.room_capacities = []
        self.exams_to_students = []
        self.student_exam_capacity = []

def read_file(filename):
    instance = Instance()
    with open(filename) as f:
        def read_attribute(name):
            line = f.readline()
            match = re.match(f'{name}:\\s*(\\d+)$', line)
            if match:
                return int(match.group(1))
            else:
                raise ValueError(f"Could not parse line {line}; expected the {name} attribute")

        instance.number_of_students = read_attribute("Number of students")
        instance.number_of_exams = read_attribute("Number of exams")
        instance.number_of_slots = read_attribute("Number of slots")
        instance.number_of_rooms = read_attribute("Number of rooms")

        for r in range(instance.number_of_rooms):
            instance.room_capacities.append(read_attribute(f"Room {r} capacity"))

        while True:
            line = f.readline()
            if line == "":
                break
            match = re.match('^\\s*(\\d+)\\s+(\\d+)\\s*$', line)
            if match:
                instance.exams_to_students.append((int(match.group(1)), int(match.group(2))))
            else:
                raise ValueError(f'Failed to parse this line: {line}')

        instance.student_exam_capacity = [0] * instance.number_of_exams
        for exam, student in instance.exams_to_students:
            instance.student_exam_capacity[exam] += 1

    return instance


def solve_with_or_tools(instance):
    model = cp_model.CpModel()

    # Variables
    exam_time = [model.NewIntVar(0, instance.number_of_slots - 1, f'exam_time_{e}') for e in range(instance.number_of_exams)]
    exam_room = [model.NewIntVar(0, instance.number_of_rooms - 1, f'exam_room_{e}') for e in range(instance.number_of_exams)]
    invigilator_assigned = [
        [
            [model.NewBoolVar(f'invigilator_{i}_exam_{e}_timeslot_{t}') for t in range(instance.number_of_slots)]
            for e in range(instance.number_of_exams)
        ]
        for i in range(10)  # Assume 10 invigilators
    ]

    # Constraints

    # Constraint 1: Each exam must be assigned to exactly one room and one timeslot
    for e in range(instance.number_of_exams):
        model.Add(exam_time[e] >= 0)
        model.Add(exam_room[e] >= 0)

    # Constraint 2: Strictly enforce no two exams can be scheduled in the same room at the same timeslot
    for e1 in range(instance.number_of_exams):
        for e2 in range(e1 + 1, instance.number_of_exams):  # Avoid duplicate pairs
            # Boolean variable for whether exams `e1` and `e2` are in the same room
            same_room = model.NewBoolVar(f'same_room_{e1}_{e2}')
            model.Add(exam_room[e1] == exam_room[e2]).OnlyEnforceIf(same_room)
            model.Add(exam_room[e1] != exam_room[e2]).OnlyEnforceIf(same_room.Not())

            # Boolean variable for whether exams `e1` and `e2` are in the same timeslot
            same_time = model.NewBoolVar(f'same_time_{e1}_{e2}')
            model.Add(exam_time[e1] == exam_time[e2]).OnlyEnforceIf(same_time)
            model.Add(exam_time[e1] != exam_time[e2]).OnlyEnforceIf(same_time.Not())

            # Ensure that if exams are in the same room, they must not be in the same timeslot
            model.AddBoolOr([same_room.Not(), same_time.Not()])

    # Constraint 3: Room Capacity
    for e in range(instance.number_of_exams):
        room_cap_constraint = [
            model.NewBoolVar(f'exam_{e}_in_room_{r}')
            for r in range(instance.number_of_rooms)
        ]
        for r in range(instance.number_of_rooms):
            model.Add(exam_room[e] == r).OnlyEnforceIf(room_cap_constraint[r])
            model.Add(instance.student_exam_capacity[e] <= instance.room_capacities[r]).OnlyEnforceIf(room_cap_constraint[r])
        model.AddBoolOr(room_cap_constraint)

    # Constraint 4: Non-overlapping exams for students
    for s in range(instance.number_of_students):
        exams_for_student = [e for e, stud in instance.exams_to_students if stud == s]
        for e1 in exams_for_student:
            for e2 in exams_for_student:
                if e1 != e2:
                    diff = model.NewIntVar(-instance.number_of_slots, instance.number_of_slots, f'diff_{e1}_{e2}')
                    abs_diff = model.NewIntVar(0, instance.number_of_slots, f'abs_diff_{e1}_{e2}')
                    model.Add(diff == exam_time[e1] - exam_time[e2])
                    model.AddAbsEquality(abs_diff, diff)
                    model.Add(abs_diff > 1)


    # Constraint 5: Dynamic invigilator assignment based on student count
    for e in range(instance.number_of_exams):
        students = instance.student_exam_capacity[e]
        required_invigilators = 1 if students <= 10 else 2 if students <= 20 else 3
        for t in range(instance.number_of_slots):
            # Create a Boolean variable for exam_time[e] == t
            exam_at_time_t = model.NewBoolVar(f'exam_{e}_at_time_{t}')
            model.Add(exam_time[e] == t).OnlyEnforceIf(exam_at_time_t)
            model.Add(exam_time[e] != t).OnlyEnforceIf(exam_at_time_t.Not())

            # Enforce invigilator constraint
            model.Add(sum(invigilator_assigned[i][e][t] for i in range(10)) == required_invigilators).OnlyEnforceIf(exam_at_time_t)


    # Constraint 6: Maximum invigilators per timeslot
    for t in range(instance.number_of_slots):
        model.Add(sum(invigilator_assigned[i][e][t] for i in range(10) for e in range(instance.number_of_exams)) <= 10)

    # Constraint 7: Each invigilator can only invigilate at most 2 exams
    for i in range(10):
        model.Add(sum(invigilator_assigned[i][e][t] for e in range(instance.number_of_exams) for t in range(instance.number_of_slots)) <= 2)

    # Constraint 8: No consecutive invigilations for invigilators
    for i in range(10):
        for t in range(instance.number_of_slots - 1):
            for e1 in range(instance.number_of_exams):
                for e2 in range(instance.number_of_exams):
                    if e1 != e2:
                        model.Add(invigilator_assigned[i][e1][t] + invigilator_assigned[i][e2][t + 1] <= 1)

    # Constraint 9: Optimal Room Allocation with Prioritization of Smallest Fit
    for e in range(instance.number_of_exams):
        # Create a list of boolean variables representing whether exam `e` is assigned to room `r`
        is_exam_in_room = [model.NewBoolVar(f'is_exam_{e}_in_room_{r}') for r in range(instance.number_of_rooms)]

        # Link `exam_room` variable to the boolean variables
        for r in range(instance.number_of_rooms):
            model.Add(exam_room[e] == r).OnlyEnforceIf(is_exam_in_room[r])
            model.Add(exam_room[e] != r).OnlyEnforceIf(is_exam_in_room[r].Not())

        # Ensure the room has enough capacity to accommodate the exam
        for r in range(instance.number_of_rooms):
            model.Add(instance.student_exam_capacity[e] <= instance.room_capacities[r]).OnlyEnforceIf(is_exam_in_room[r])

        # Add constraint to prioritize the smallest room that can accommodate the exam
        for r1 in range(instance.number_of_rooms):
            for r2 in range(instance.number_of_rooms):
                if r1 != r2 and instance.room_capacities[r1] < instance.room_capacities[r2]:
                    # If room r1 can accommodate the exam and room r2 can also accommodate the exam,
                    # then r2 cannot be selected if r1 is available
                    model.Add(is_exam_in_room[r2] == 0).OnlyEnforceIf([
                        is_exam_in_room[r1],  # r1 is selected
                        instance.student_exam_capacity[e] <= instance.room_capacities[r1],
                        instance.student_exam_capacity[e] <= instance.room_capacities[r2]
                    ])

    # Solver
    solver = cp_model.CpSolver()
    start_time = time.time()  # Start timing
    status = solver.Solve(model)
    end_time = time.time()  # End timing
    elapsed_time_ms = (end_time - start_time) * 1000  # Calculate time in milliseconds

    # Output results
    if status == cp_model.FEASIBLE or status == cp_model.OPTIMAL:
        print(f"Time taken to solve: {elapsed_time_ms:.2f} ms")
        print("Solution found:")
        for e in range(instance.number_of_exams):
            print(f'Exam {e}: Time = {solver.Value(exam_time[e])}, Room = {solver.Value(exam_room[e])}')
        for i in range(10):
            for e in range(instance.number_of_exams):
                for t in range(instance.number_of_slots):
                    if solver.Value(invigilator_assigned[i][e][t]) == 1:
                        print(f'Invigilator {i} is assigned to Exam {e} at Timeslot {t}')
    else:
        print(f"Time taken to solve: {elapsed_time_ms:.2f} ms")
        print("No feasible solution found.")

def process_and_solve_all_instances(directory):
    files = sorted([f for f in os.listdir(directory) if f.endswith(".txt")])
    for filename in files:
        filepath = os.path.join(directory, filename)
        try:
            print(f"\nProcessing file: {filename}")
            instance = read_file(filepath)
            solve_with_or_tools(instance)
        except Exception as e:
            print(f"Error processing {filename}: {e}")


test_instances_folder = "./test instances"
process_and_solve_all_instances(test_instances_folder)
