export const BMC_EXPECTED_VERDICTS = new Set(['counterexample', 'proved']);

export function bmcRunPasses(lesson, result) {
  if (lesson?.bmcExpected) return result?.verdict === lesson.bmcExpected;
  return result?.ok === true;
}
