/**
 * This file is part of CamImportPlugins/SotonImportPlugins.
 * 
 * Copyright (C) 2011 intranda GmbH
 * 
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * @author Andrey Kozhushkov
 */
package de.intranda.goobi.plugins.utils;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.apache.commons.lang.StringUtils;
import org.apache.log4j.Logger;
import org.apache.poi.hdf.model.hdftypes.FileInformationBlock;
import org.apache.poi.hssf.record.chart.SeriesIndexRecord;
import org.jdom.Document;
import org.jdom.Element;
import org.jdom.JDOMException;
import org.jdom.Namespace;
import org.jdom.input.SAXBuilder;
import org.jdom.output.XMLOutputter;
import org.jdom.xpath.XPath;

import de.schlichtherle.io.FileInputStream;
import de.sub.goobi.Import.ImportOpac;

import ugh.dl.DocStruct;
import ugh.dl.Metadata;
import ugh.dl.MetadataType;
import ugh.dl.Person;
import ugh.dl.Prefs;
import ugh.exceptions.DocStructHasNoTypeException;
import ugh.exceptions.MetadataTypeNotAllowedException;

public class ModsUtils {

	/** Logger for this class. */
	private static final Logger logger = Logger.getLogger(ModsUtils.class);

	private static final Namespace NS_MODS = Namespace.getNamespace("mods", "http://www.loc.gov/mods/v3");

	private static HashMap<String, String> seriesInfo = new HashMap<String, String>(); // Name and identifier of related Item "series"
	private static String seriesInfoFilename = "seriesInfo.ser";

	/**
	 * Writes the given JDOM document into a file.
	 * 
	 * @param folderName
	 *            Folder in which to write the destination file.
	 * @param fileName
	 *            Name of the destination file.
	 * @param doc
	 *            JDOM document containing the data.
	 * @throws FileNotFoundException
	 * @throws IOException
	 */
	public static void writeXmlToFile(String folderName, String fileName, Document doc) {
		try {
			File folder = new File(folderName);
			if (!folder.exists()) {
				folder.mkdirs();
			}
			new XMLOutputter().output(doc, new FileOutputStream(folder.getAbsolutePath() + File.separator + fileName));
		} catch (FileNotFoundException e) {
			logger.error(e.getMessage());
		} catch (IOException e) {
			logger.error(e.getMessage());
		}
	}

	private static void writeFile(File file, Object obj) {
		try {
			FileOutputStream fs = new FileOutputStream(file);
			ObjectOutputStream os = new ObjectOutputStream(fs);
			os.writeObject(obj);
			os.close();
		} catch (IOException e) {
			logger.error("Error writing binary file", e);
		}
	}

	public static Document createEmptyGoobiDoc(Namespace mets, Namespace mods, Namespace goobi) {
		Document doc = new Document();

		doc.setRootElement(new Element("mets", mets));
		Element root = doc.getRootElement();
		Element dmdSec = new Element("dmdSec", mets);
		dmdSec.setAttribute("ID", "DMDLOG_0000");
		root.addContent(dmdSec);
		Element mdWrap = new Element("mdWrap", mets);
		mdWrap.setAttribute("MDTYPE", "MODS");
		dmdSec.addContent(mdWrap);
		Element xmlData = new Element("xmlData", mets);
		mdWrap.setContent(xmlData);
		Element modsEle = new Element("mods", mods);
		xmlData.setContent(modsEle);
		Element extension = new Element("extension", mods);
		modsEle.addContent(extension);
		Element goobiEle = new Element("goobi", goobi);
		extension.addContent(goobiEle);
		Element dmdSec2 = new Element("dmdSec", mets);
		dmdSec.setAttribute("ID", "DMDPHYS_0000");
		root.addContent(dmdSec2);
		Element mdWrap2 = new Element("mdWrap", mets);
		mdWrap.setAttribute("MDTYPE", "MODS");
		dmdSec2.addContent(mdWrap2);
		Element xmlData2 = new Element("xmlData", mets);
		mdWrap2.setContent(xmlData2);
		Element modsEle2 = new Element("mods", mods);
		xmlData2.setContent(modsEle2);
		Element extension2 = new Element("extension", mods);
		modsEle2.addContent(extension2);
		Element goobiEle2 = new Element("goobi", goobi);
		extension2.addContent(goobiEle2);

		return doc;

	}

	private static Object readFile(File file) {
		FileInputStream fis;
		Object obj = null;
		try {
			fis = new FileInputStream(file);
			ObjectInputStream ois = new ObjectInputStream(fis);
			obj = ois.readObject();
			ois.close();
		} catch (FileNotFoundException e) {
			logger.warn("No binary file exists to read. Aborting.");
		} catch (IOException e) {
			logger.error("Error reading binary file", e);
		} catch (ClassNotFoundException e) {
			logger.error("Error reading object from binary file", e);
		}
		return obj;
	}

	/**
	 * 
	 * @param pres
	 * @param dsLogical
	 * @param dsPhysical
	 * @param eleMods
	 * @param mappingFile
	 * @throws IOException
	 * @throws JDOMException
	 */
	@SuppressWarnings("unchecked")
	public static void parseModsSection(String mappingFileName, Prefs prefs, DocStruct dsLogical, DocStruct dsPhysical, DocStruct dsSeries, Element eleMods) throws JDOMException,
			IOException {
		// logger.debug(new XMLOutputter().outputString(eleMods));
		File mappingFile = new File(mappingFileName);
		

		// Get seriesInfo from File
		File tempDir = new File(mappingFile.getParentFile().getParentFile(), "temp");
		if (!tempDir.isDirectory()) {
			tempDir.mkdirs();
		}
		File seriesInfoFile = new File(tempDir, seriesInfoFilename);
		if (seriesInfoFile.isFile()) {
			logger.debug("Reading data from " + seriesInfoFile.getName());
			Object obj = readFile(seriesInfoFile);
			if (obj instanceof HashMap<?, ?>) {
				seriesInfo = (HashMap<String, String>) obj;
			}
		}

		Document doc = new Document();
		Element eleNewMods = (Element) eleMods.clone();
		doc.setRootElement(eleNewMods);
		Document mapDoc = new SAXBuilder().build(mappingFile);
		for (Object obj : mapDoc.getRootElement().getChildren("metadata", null)) {
			Element eleMetadata = (Element) obj;
			String mdName = eleMetadata.getChildTextTrim("name", null);

			// Code to handle related works, e.g. series
			if (mdName.contentEquals("relatedSeries")) {
				List<Element> eleXpathList = eleMetadata.getChildren("xpath", null);
				for (Element eleXpath : eleXpathList) {
					String query = eleXpath.getTextTrim();
					// logger.debug("XPath: " + query);
					XPath xpath = XPath.newInstance(query);
					xpath.addNamespace(NS_MODS);
					List<Element> eleValueList = xpath.selectNodes(doc);
					if (eleValueList != null && !eleValueList.isEmpty()) {
						List<String> values = new ArrayList<String>();
						for (Element eleValue : eleValueList) {
							// logger.debug("Value: " + eleValue.getTextTrim());
							values.add(eleValue.getTextTrim());
						}

						String value = "";
						for (String s : values) {
							if (StringUtils.isNotEmpty(s)) {
								value += " " + s;
							}
						}
						value = value.trim();
						String[] valueParts = value.split("\\s");
						String seriesName = "";
						for (int i = 0; i < valueParts.length; i++) {
							seriesName += " " + valueParts[i];
						}
						seriesName = seriesName.trim();
						logger.debug("related Series = " + seriesName);
						String seriesID = seriesInfo.get(seriesName);
						if (seriesID == null) {
							seriesID = "CSIC" + System.currentTimeMillis();
							logger.debug("Series not found. creating new one: " + seriesID);
							seriesInfo.put(seriesName, seriesID);
						}

						// Creating metadata for series
						try {
							MetadataType titleType = prefs.getMetadataTypeByName("TitleDocMain");
							MetadataType idType = prefs.getMetadataTypeByName("CatalogIDDigital");
							Metadata mdTitle;
							mdTitle = new Metadata(titleType);
							Metadata mdID = new Metadata(idType);
							mdTitle.setValue(seriesName);
							mdID.setValue(seriesID);

							logger.debug("Found metadata: " + mdTitle.getType().getName());
							if (eleMetadata.getAttribute("logical") != null && eleMetadata.getAttributeValue("logical").equalsIgnoreCase("true")) {
								logger.debug("Added metadata \"" + mdTitle.getValue() + "\" to logical structure");
								dsSeries.addMetadata(mdTitle);
							}
							logger.debug("Found metadata: " + mdID.getType().getName());
							if (eleMetadata.getAttribute("logical") != null && eleMetadata.getAttributeValue("logical").equalsIgnoreCase("true")) {
								logger.debug("Added metadata \"" + mdID.getValue() + "\" to logical structure");
								dsSeries.addMetadata(mdID);
							}
							
						} catch (MetadataTypeNotAllowedException e) {
							logger.error(e.toString(), e);
						}
					}
				}
			}

			MetadataType mdType = prefs.getMetadataTypeByName(mdName);
			if (mdType != null) {
				try {
					List<Element> eleXpathList = eleMetadata.getChildren("xpath", null);
					if (mdType.getIsPerson()) {
						// Persons
						for (Element eleXpath : eleXpathList) {
							String query = eleXpath.getTextTrim();
							// logger.debug("XPath: " + query);
							XPath xpath = XPath.newInstance(query);
							xpath.addNamespace(NS_MODS);
							// Element eleValue = (Element) xpath.selectSingleNode(doc);
							List<Element> eleValueList = xpath.selectNodes(doc);
							if (eleValueList != null) {
								for (Element eleValue : eleValueList) {
									String name = "";
									String firstName = "";
									String lastName = "";

									if (eleXpath.getAttribute("family") != null) {
										lastName = eleValue.getTextTrim();
									} else if (eleXpath.getAttribute("given") != null) {
										firstName = eleValue.getTextTrim();
									} else {
										name = eleValue.getTextTrim();
									}

									if (name.contains(",")) {
										String[] nameSplit = name.split("[,]");
										if (nameSplit.length > 0 && StringUtils.isEmpty(lastName)) {
											lastName = nameSplit[0].trim();
										}
										if (nameSplit.length > 1 && StringUtils.isEmpty(firstName)) {
											firstName = nameSplit[1].trim();
										}
									} else {
										lastName = name;
									}

									if (StringUtils.isNotEmpty(lastName)) {
										Person person = new Person(mdType);
										person.setFirstname(firstName);
										person.setLastname(lastName);
										person.setRole(mdType.getName());
										if (eleMetadata.getAttribute("logical") != null && eleMetadata.getAttributeValue("logical").equalsIgnoreCase("true")) {
											dsLogical.addPerson(person);
										}
									}
								}
							}
						}

					} else {
						// Regular metadata
						String titleArticle = null, title = null;
						String id1 = null, id2 = null;
						for (Element eleXpath : eleXpathList) {
							String query = eleXpath.getTextTrim();
							// logger.debug("XPath: " + query);
							XPath xpath = XPath.newInstance(query);
							xpath.addNamespace(NS_MODS);
							List<Element> eleValueList = xpath.selectNodes(doc);
							if (eleValueList != null) {
								List<String> values = new ArrayList<String>();
								for (Element eleValue : eleValueList) {

									// logger.debug("mdType: " + mdType.getName() + "; Value: " + eleValue.getTextTrim());
									// values.add(eleValue.getTextTrim());
									// String value = "";
									// for (String s : values) {
									// if (StringUtils.isNotEmpty(s)) {
									// value += " " + s;
									// }
									// }
									// value = value.trim();
									String value = eleValue.getTextTrim();

									// if we have the title, get both nonSort (article) and title before writing metadata
									if (mdType.getName().contentEquals("TitleDocMain")) {
										if (eleXpath.getValue().contains("nonSort")) {
											titleArticle = value;
										} else if (eleXpath.getValue().contains("title")) {
											title = value;
										}
										if (titleArticle != null && title != null) {
											value = titleArticle + " " + title;
										} else if (title != null) {
											value = title;
										} else
											continue;
									}
									
									//Add singleDigCollection to series also
									if(mdType.getName().contentEquals("singleDigCollection"))
									{
										if (value.length() > 0) {
											Metadata metadata = new Metadata(mdType);
											metadata.setValue(value);
											logger.debug("Found metadata: " + metadata.getType().getName());
											if (eleMetadata.getAttribute("logical") != null && eleMetadata.getAttributeValue("logical").equalsIgnoreCase("true")) {
												logger.debug("Added metadata \"" + metadata.getValue() + "\" to logical structure");
												dsSeries.addMetadata(metadata);
											}
										}
									}

									if (value.length() > 0) {
										Metadata metadata = new Metadata(mdType);
										metadata.setValue(value);
										logger.debug("Found metadata: " + metadata.getType().getName());
										if (eleMetadata.getAttribute("logical") != null && eleMetadata.getAttributeValue("logical").equalsIgnoreCase("true")) {
											logger.debug("Added metadata \"" + metadata.getValue() + "\" to logical structure");
											dsLogical.addMetadata(metadata);
										}
										if (eleMetadata.getAttribute("physical") != null && eleMetadata.getAttributeValue("physical").equalsIgnoreCase("true")) {
											logger.debug("Added metadata \"" + metadata.getValue() + "\" to physical structure");
											dsPhysical.addMetadata(metadata);
										}
									}
								}
							}
						}
					}
				} catch (MetadataTypeNotAllowedException e) {
					logger.warn(e.getMessage());
				}
			} else {
				logger.warn("Metadata '" + mdName + "' is not defined in the ruleset.");
			}
		}

		// write seriesInfo to file
		if (seriesInfoFile.isFile()) {
			logger.debug("deleting old seriesInfoFile");
			seriesInfoFile.delete();
		}
		writeFile(seriesInfoFile, seriesInfo);
	}

	/**
	 * 
	 * @param dsLogical
	 * @param dsPhysical
	 * @param eleMods
	 * @throws MetadataTypeNotAllowedException
	 */
	@Deprecated
	public static void parseModsSectionOld(Prefs prefs, DocStruct dsLogical, DocStruct dsPhysical, Element eleMods) {
		for (Object objMeta : eleMods.getChildren()) {
			try {
				Element eleMeta = (Element) objMeta;
				// logger.debug("md: " + eleMeta.getName());
				if (eleMeta.getName().equals("titleInfo")) {
					String localTitle = "";
					if (eleMeta.getChild("nonSort", null) != null) {
						localTitle += eleMeta.getChild("nonSort", null).getText();
					}
					if (eleMeta.getChild("title", null) != null) {
						localTitle += eleMeta.getChild("title", null).getText();
					}
					logger.debug("LocalTitle = " + localTitle);
					if (eleMeta.getAttribute("type") != null) {
						if (eleMeta.getAttributeValue("type").equals("alternative")) {
							Metadata mdTitle = new Metadata(prefs.getMetadataTypeByName("TitleDocParallel"));
							dsLogical.addMetadata(mdTitle);
							mdTitle.setValue(localTitle);
						}
					} else {
						// Main title
						// currentTitle = localTitle;
						Metadata mdTitle = new Metadata(prefs.getMetadataTypeByName("TitleDocMain"));
						dsLogical.addMetadata(mdTitle);
						mdTitle.setValue(localTitle);
						if (eleMeta.getChild("subTitle", null) != null) {
							// Main subtitle
							Metadata mdSubTitle = new Metadata(prefs.getMetadataTypeByName("TitleDocSub1"));
							dsLogical.addMetadata(mdSubTitle);
							mdSubTitle.setValue(eleMeta.getChild("subTitle", null).getTextTrim());
						}
					}

				} else if (eleMeta.getName().equals("name")) {
					if (eleMeta.getAttributeValue("type").equals("personal")) {
						String name = "";
						String lastName = "";
						String firstName = "";
						for (Object obj : eleMeta.getChildren("namePart", null)) {
							Element eleNamePart = (Element) obj;
							if (eleNamePart.getAttribute("type") != null) {
								if (eleNamePart.getAttributeValue("type").equals("family")) {
									lastName = eleMeta.getChild("namePart", null).getAttributeValue("type");
								} else if (eleNamePart.getAttributeValue("type").equals("given")) {
									firstName = eleMeta.getChild("namePart", null).getAttributeValue("type");
								} else if (eleNamePart.getAttributeValue("type").equals("date")) {
									// TODO currently not supported by the ruleset
								}
							} else {
								name += eleMeta.getChild("namePart", null).getText();
							}
						}
						if (name.contains(",")) {
							String[] nameSplit = name.split("[,]");
							if (nameSplit.length > 0 && StringUtils.isEmpty(lastName)) {
								lastName = nameSplit[0].trim();
							}
							if (nameSplit.length > 1 && StringUtils.isEmpty(firstName)) {
								firstName = nameSplit[1].trim();
							}
						} else {
							lastName = name;
						}

						Person person = new Person(prefs.getMetadataTypeByName("Author"));
						dsLogical.addPerson(person);
						person.setFirstname(firstName);
						person.setLastname(lastName);
						person.setRole("Author");
					} else if (eleMeta.getAttributeValue("type").equals("corporate")) {
						// TODO currently not supported by the ruleset
					}
				} else if (eleMeta.getName().equals("originInfo")) {
					for (Object obj : eleMeta.getChildren()) {
						Element ele = (Element) obj;
						if (ele.getName().equals("place")) {
							Element elePlaceTerm = ele.getChild("placeTerm", null);
							if (elePlaceTerm != null && elePlaceTerm.getAttribute("type") != null) {
								if (elePlaceTerm.getAttributeValue("type").equals("text")) {
									Metadata metadata = new Metadata(prefs.getMetadataTypeByName("PlaceOfPublication"));
									dsLogical.addMetadata(metadata);
									metadata.setValue(elePlaceTerm.getTextTrim());
								} else if (elePlaceTerm.getAttributeValue("type").equals("code")) {
									// TODO currently not supported by the ruleset
								}
							}
						} else if (ele.getName().equals("publisher")) {
							Metadata metadata = new Metadata(prefs.getMetadataTypeByName("PublisherName"));
							dsLogical.addMetadata(metadata);
							metadata.setValue(ele.getTextTrim());
						} else if (ele.getName().equals("dateIssued")) {
							if (ele.getAttribute("point") != null) {
								if (ele.getAttributeValue("point").equals("start")) {
									Metadata metadata = new Metadata(prefs.getMetadataTypeByName("PublicationStart"));
									dsLogical.addMetadata(metadata);
									metadata.setValue(ele.getTextTrim());
								} else if (ele.getAttributeValue("point").equals("end")) {
									Metadata metadata = new Metadata(prefs.getMetadataTypeByName("PublicationEnd"));
									dsLogical.addMetadata(metadata);
									metadata.setValue(ele.getTextTrim());
								}
							} else {
								Metadata metadata = new Metadata(prefs.getMetadataTypeByName("PublicationYear"));
								dsLogical.addMetadata(metadata);
								metadata.setValue(ele.getTextTrim());
							}
						} else if (ele.getName().equals("dateCreated")) {
							Metadata metadata = new Metadata(prefs.getMetadataTypeByName("PublicationYear"));
							dsLogical.addMetadata(metadata);
							metadata.setValue(ele.getTextTrim());
						}
					}
				} else if (eleMeta.getName().equals("language")) {
					Element eleLanguageTerm = eleMeta.getChild("languageTerm", null);
					if (eleLanguageTerm != null && eleLanguageTerm.getAttribute("authority") != null
							&& eleLanguageTerm.getAttributeValue("authority").equals("iso639-2b")) {
						String language = eleMeta.getChildTextTrim("languageTerm", null);
						Metadata metadata = new Metadata(prefs.getMetadataTypeByName("DocLanguage"));
						dsLogical.addMetadata(metadata);
						metadata.setValue(language);
					}
				} else if (eleMeta.getName().equals("physicalDescription")) {
					for (Object obj : eleMeta.getChildren()) {
						Element ele = (Element) obj;
						if (ele.getName().equals("extent")) {
							Metadata metadata = new Metadata(prefs.getMetadataTypeByName("SizeSourcePrint"));
							dsLogical.addMetadata(metadata);
							metadata.setValue(ele.getTextTrim());
						}
					}
				} else if (eleMeta.getName().equals("recordInfo")) {
					for (Object obj : eleMeta.getChildren()) {
						Element ele = (Element) obj;
						if (ele.getName().equals("recordIdentifier")) {
							Metadata metadata = new Metadata(prefs.getMetadataTypeByName("CatalogIDDigital"));
							dsLogical.addMetadata(metadata);
							metadata.setValue(ele.getTextTrim());
							// currentIdentifier = metadata.getValue();
						}
					}
				} else if (eleMeta.getName().equals("location")) {
					for (Object obj : eleMeta.getChildren()) {
						Element ele = (Element) obj;
						if (ele.getName().equals("physicalLocation")) {
							Metadata metadata = new Metadata(prefs.getMetadataTypeByName("physicallocation"));
							dsLogical.addMetadata(metadata);
							dsPhysical.addMetadata(metadata);
							metadata.setValue(ele.getTextTrim());
						} else if (ele.getName().equals("shelfLocation")) {
							Metadata metadata = new Metadata(prefs.getMetadataTypeByName("shelfmarksource"));
							dsLogical.addMetadata(metadata);
							dsPhysical.addMetadata(metadata);
							metadata.setValue(ele.getTextTrim());
						}
					}
				}
			} catch (MetadataTypeNotAllowedException e) {
				logger.warn(e.getMessage());
			}
		}
	}

	/**
	 * Returns the document's identifier, or a timestamp if the record has none
	 * 
	 * @param prefs
	 * @param ds
	 * @return
	 * @throws MetadataTypeNotAllowedException
	 * @throws DocStructHasNoTypeException
	 */
	public static String getIdentifier(Prefs prefs, DocStruct ds) throws MetadataTypeNotAllowedException, DocStructHasNoTypeException {
		String ret = null;

		MetadataType mdTypeId = prefs.getMetadataTypeByName("CatalogIDDigital");
		if (ds.getAllMetadataByType(mdTypeId) != null && !ds.getAllMetadataByType(mdTypeId).isEmpty()) {
			Metadata mdId = ds.getAllMetadataByType(mdTypeId).get(0);
			ret = mdId.getValue();
		} else {
			Metadata mdId = new Metadata(mdTypeId);
			ds.addMetadata(mdId);
			mdId.setValue(String.valueOf(System.currentTimeMillis()));
			ret = mdId.getValue();
		}

		return ret;
	}

	/**
	 * Returns the document's title.
	 * 
	 * @param prefs
	 * @param ds
	 * @return
	 * @throws MetadataTypeNotAllowedException
	 * @throws DocStructHasNoTypeException
	 */
	public static String getTitle(Prefs prefs, DocStruct ds) throws MetadataTypeNotAllowedException, DocStructHasNoTypeException {
		String ret = null;

		MetadataType mdTypeTitle = prefs.getMetadataTypeByName("TitleDocMain");
		if (ds.getAllMetadataByType(mdTypeTitle) != null && !ds.getAllMetadataByType(mdTypeTitle).isEmpty()) {
			Metadata mdTitle = ds.getAllMetadataByType(mdTypeTitle).get(0);
			ret = mdTitle.getValue();
		}

		return ret;
	}

	/**
	 * Returns the document's author.
	 * 
	 * @param prefs
	 * @param ds
	 * @return
	 * @throws MetadataTypeNotAllowedException
	 * @throws DocStructHasNoTypeException
	 */
	public static String getAuthor(Prefs prefs, DocStruct ds) throws MetadataTypeNotAllowedException, DocStructHasNoTypeException {
		String ret = null;

		MetadataType mdTypePerson = prefs.getMetadataTypeByName("Author");
		if (ds.getAllPersonsByType(mdTypePerson) != null && !ds.getAllPersonsByType(mdTypePerson).isEmpty()) {
			Person personAuthor = ds.getAllPersonsByType(mdTypePerson).get(0);
			ret = personAuthor.getLastname();
			if (StringUtils.isNotEmpty(personAuthor.getFirstname())) {
				ret += ", " + personAuthor.getFirstname();
			}
		}

		return ret;
	}
}
