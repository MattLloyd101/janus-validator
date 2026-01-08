export * from "./types";
export * from "./Domain";
export * from "./domains/FiniteDomain";
export * from "./domains/ContiguousDomain";
export * from "./domains/BigIntDomain";
export * from "./domains/BytesDomain";
export * from "./domains/StringDomain";
export * from "./domains/RegexDomain";
export * from "./domains/StructDomain";
export * from "./domains/QuantifierDomain";
export * from "./domains/AlternationDomain";
export * from "./domains/SequenceDomain";
export * from "./domains/CustomGeneratorDomain";
export * from "./domains/TransformDomain";
export * from "./relations/encapsulates";
export * from "./set/operations";
export * from "./generators";

import { encapsulates } from "./relations/encapsulates";
import { union, intersect, subtract } from "./set/operations";

export const Domains = {
  relations: { encapsulates },
  set: { union, intersect, subtract },
};

