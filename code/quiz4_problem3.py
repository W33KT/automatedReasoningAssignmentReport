import itertools


attendees = {
    (0,1): [1,2,3,4,6],
    (0,4): [0,5,7,8,9],
    (1,1): [0,2,3,5,7],
    (1,4): [1,4,6,8,9],
    (2,2): [0,2,4,5,8],
    (2,3): [1,3,6,7,9],
    (3,0): [0,1,3,4,9],
    (3,3): [2,5,6,7,8],
    (4,0): [0,1,2,7,8],
    (4,2): [3,4,5,6,9]
}

distinct_pairs = set()

for (course, house), participants in attendees.items():
    guests = [p for p in participants]
    
    for pair in itertools.combinations(guests, 2):
        distinct_pairs.add(tuple(sorted(pair)))

print("Number of distinct guest pairings:", len(distinct_pairs))
print("All distinct pairs:", distinct_pairs)