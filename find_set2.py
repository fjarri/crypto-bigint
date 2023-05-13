import numpy
import pygad


N = 256
#size = 30

target = set(range(N))

def fitness_func(ga_instance, solution, solution_idx):
    s = set(solution)
    extras = len(solution) - len(s)

    s.add(0)
    s.add(1)

    temp = numpy.zeros(N, numpy.uint8)
    for i in s:
        for j in s:
            if i + j < N:
                temp[i+j] = 1

    return (temp.sum() / N) ** 2 * min(2, extras + 1)


s = list(range(2, 16)) + list(range(16, N, 16))
#print(fitness_func(None, numpy.array(s), None))
#exit(0)


ga_instance = pygad.GA(num_generations=1000,
                       num_parents_mating=4,
                       fitness_func=fitness_func,
                       initial_population=numpy.array(s).reshape(1, len(s)).repeat(1000, axis=0),
                       #sol_per_pop=200,
                       #num_genes=size,
                       gene_type=int,
                       init_range_low=2,
                       init_range_high=N-1,
                       parent_selection_type="sss",
                       keep_parents=1,
                       crossover_type="single_point",
                       mutation_type="random",
                       mutation_percent_genes=20,
                       stop_criteria=[f"reach_2"],
                       gene_space=list(range(2, N)),
                       parallel_processing=["thread", 10])

ga_instance.run()

solution, solution_fitness, solution_idx = ga_instance.best_solution()
print(f"Parameters of the best solution : {list(sorted(solution))}")
print(f"Fitness value of the best solution = {fitness_func(None, solution, None)}")

s = set(solution)
s.add(0)
s.add(1)
all_sums = set(i + j for i in s for j in s)
missing = target - all_sums
print("Missing:", missing)
print(list(sorted(s)))
